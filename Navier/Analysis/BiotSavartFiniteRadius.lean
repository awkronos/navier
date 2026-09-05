import Navier.Analysis.BiotSavartIntegrationByParts
import Navier.Analysis.BiotSavartPuncture
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth finite-radius Biot--Savart punctures

This file constructs a canonical smooth exterior cutoff that vanishes on an
actual Euclidean ball.  It instantiates the off-origin integration-by-parts
theorem with this cutoff, leaving no differentiability or integrability
hypotheses on the cutoff layer.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace Navier.Analysis.BiotSavartFiniteRadius

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding

/-- Squared Euclidean radius, used so the cutoff is smooth at the origin. -/
def radiusSq (x : Space) : ℝ := ∑ k : Fin 3, x k ^ 2

theorem radiusSq_eq_officialEuclideanNorm_sq (x : Space) :
    radiusSq x = officialEuclideanNorm x ^ 2 := by
  rw [radiusSq, officialEuclideanNorm_eq_sqrt_sum_sq,
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg |x k|)]
  simp only [sq_abs]

private theorem continuous_radiusSq : Continuous radiusSq := by
  unfold radiusSq
  fun_prop

private theorem differentiable_radiusSq : Differentiable ℝ radiusSq := by
  unfold radiusSq
  fun_prop

/-- A smooth cutoff equal to zero on `|x| ≤ ε` and one on
`|x|² ≥ 2ε²`. -/
def smoothExteriorCutoff (ε : ℝ) (x : Space) : ℝ :=
  Real.smoothTransition (radiusSq x / ε ^ 2 - 1)

theorem continuous_smoothExteriorCutoff (ε : ℝ) :
    Continuous (smoothExteriorCutoff ε) := by
  exact Real.smoothTransition.continuous.comp
    ((continuous_radiusSq.div_const _).sub continuous_const)

theorem differentiable_smoothExteriorCutoff (ε : ℝ) :
    Differentiable ℝ (smoothExteriorCutoff ε) := by
  unfold smoothExteriorCutoff
  have hs : ContDiff ℝ 1 Real.smoothTransition :=
    Real.smoothTransition.contDiff
  apply (hs.differentiable (by norm_num)).comp
  unfold radiusSq
  fun_prop

theorem smoothExteriorCutoff_eq_zero {ε : ℝ} (hε : 0 < ε)
    {x : Space} (hx : officialEuclideanNorm x ≤ ε) :
    smoothExteriorCutoff ε x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [radiusSq_eq_officialEuclideanNorm_sq]
  have hsq : officialEuclideanNorm x ^ 2 ≤ ε ^ 2 :=
    (sq_le_sq₀ (officialEuclideanNorm_nonneg x) hε.le).2 hx
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [sub_nonpos, div_le_one hεsq]
  exact hsq

/-- The topological support of the smooth exterior cutoff avoids the origin. -/
theorem zero_not_mem_tsupport_smoothExteriorCutoff {ε : ℝ} (hε : 0 < ε) :
    (0 : Space) ∉ tsupport (smoothExteriorCutoff ε) := by
  intro hmem
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hrad : 0 < ε / Real.sqrt 3 := div_pos hε hsqrt
  have hball : Metric.ball (0 : Space) (ε / Real.sqrt 3) ∈ nhds (0 : Space) :=
    Metric.ball_mem_nhds _ hrad
  obtain ⟨x, hxBall, hxSupport⟩ :=
    (mem_closure_iff_nhds.1 hmem) _ hball
  have hnorm : officialEuclideanNorm x < ε := by
    have hprod := officialEuclideanNorm_le x
    have hxnorm : ‖x‖ < ε / Real.sqrt 3 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxBall
    calc
      officialEuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := hprod
      _ < Real.sqrt 3 * (ε / Real.sqrt 3) :=
        mul_lt_mul_of_pos_left hxnorm hsqrt
      _ = ε := by field_simp
  have hzero : smoothExteriorCutoff ε x = 0 :=
    smoothExteriorCutoff_eq_zero hε hnorm.le
  exact hxSupport hzero

theorem tsupport_smoothExteriorCutoff_away {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ tsupport (smoothExteriorCutoff ε), x ≠ 0 := by
  intro x hx hxeq
  subst x
  exact zero_not_mem_tsupport_smoothExteriorCutoff hε hx

private theorem radiusSq_coordinateLine_hasDerivAt (x : Space) (i : Fin 3) :
    HasDerivAt
      (∑ k : Fin 3, (fun t : ℝ => x k + t * basisVector i k) ^ 2)
      (2 * x i) 0 := by
  classical
  have hsum := HasDerivAt.sum (x := (0 : ℝ)) (u := Finset.univ)
      (A := fun k : Fin 3 => (fun t : ℝ => x k + t * basisVector i k) ^ 2)
      (A' := fun k : Fin 3 => 2 * x k * basisVector i k)
      (fun k _ => by
        have hlin : HasDerivAt (fun t : ℝ => x k + t * basisVector i k)
            (basisVector i k) 0 := by
          simpa only [id_eq, mul_one, add_zero, mul_comm] using
            (hasDerivAt_id 0).mul_const (basisVector i k) |>.const_add (x k)
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, add_zero]
          using hlin.pow 2)
  have hdelta : (∑ k : Fin 3, 2 * x k * basisVector i k) = 2 * x i := by
    simp [basisVector, Pi.single_apply]
  rw [← hdelta]
  exact hsum

/-- Exact coordinate derivative of the smooth exterior cutoff. -/
theorem smoothExteriorCutoff_fderiv_basis (ε : ℝ)
    (x : Space) (i : Fin 3) :
    fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) =
      deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
        (2 * x i / ε ^ 2) := by
  have hradius : HasDerivAt (fun t : ℝ =>
      radiusSq (x + t • basisVector i)) (2 * x i) 0 := by
    have hr := radiusSq_coordinateLine_hasDerivAt x i
    convert hr using 1
    funext t
    simp only [radiusSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Pi.pow_apply]
  have hinner : HasDerivAt
      (fun t : ℝ => radiusSq (x + t • basisVector i) / ε ^ 2 - 1)
      (2 * x i / ε ^ 2) 0 :=
    (hradius.div_const (ε ^ 2)).sub_const 1
  have hs : DifferentiableAt ℝ Real.smoothTransition
      (radiusSq x / ε ^ 2 - 1) := by
    have hs' : ContDiff ℝ 1 Real.smoothTransition :=
      Real.smoothTransition.contDiff
    have hd : Differentiable ℝ Real.smoothTransition :=
      hs'.differentiable (by norm_num)
    exact hd _
  have hformula : HasDerivAt
      (smoothExteriorCutoff ε ∘ fun t : ℝ => x + t • basisVector i)
      (deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
        (2 * x i / ε ^ 2)) 0 := by
    have hs0 : DifferentiableAt ℝ Real.smoothTransition
        (radiusSq (x + (0 : ℝ) • basisVector i) / ε ^ 2 - 1) := by
      simpa only [zero_smul, add_zero] using hs
    have hc := hs0.hasDerivAt.comp 0 hinner
    have hc' : HasDerivAt
        (Real.smoothTransition ∘ fun t : ℝ =>
          radiusSq (x + t • basisVector i) / ε ^ 2 - 1)
        (deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
          (2 * x i / ε ^ 2)) 0 := by
      simpa only [zero_smul, add_zero] using hc
    apply hc'.congr_of_eventuallyEq
    exact Eventually.of_forall fun _ => rfl
  have hline : HasDerivAt (fun t : ℝ => x + t • basisVector i)
      (basisVector i) 0 := by
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (basisVector i) |>.const_add x
  have hfromFDeriv : HasDerivAt
      (smoothExteriorCutoff ε ∘ fun t : ℝ => x + t • basisVector i)
      (fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i)) 0 := by
    have hcut : HasFDerivAt (smoothExteriorCutoff ε)
        (fderiv ℝ (smoothExteriorCutoff ε) x)
        (x + (0 : ℝ) • basisVector i) := by
      simpa only [zero_smul, add_zero] using
        (differentiable_smoothExteriorCutoff ε x).hasFDerivAt
    exact hcut.comp_hasDerivAt 0 hline
  exact hfromFDeriv.unique hformula

private theorem differentiableAt_officialEuclideanNorm {x : Space} (hx : x ≠ 0) :
    DifferentiableAt ℝ officialEuclideanNorm x := by
  have hradius_ne : radiusSq x ≠ 0 := by
    intro hr
    apply hx
    apply norm_eq_zero.mp
    have hnorm := norm_le_officialEuclideanNorm x
    have hoff : officialEuclideanNorm x = 0 := by
      have hsquare : officialEuclideanNorm x ^ 2 = 0 := by
        rw [← radiusSq_eq_officialEuclideanNorm_sq, hr]
      nlinarith [officialEuclideanNorm_nonneg x]
    rw [hoff] at hnorm
    exact le_antisymm hnorm (norm_nonneg x)
  rw [show officialEuclideanNorm = fun y : Space => Real.sqrt (radiusSq y) by
    funext y
    rw [officialEuclideanNorm_eq_sqrt_sum_sq, radiusSq]
    simp only [sq_abs]]
  exact (Real.hasDerivAt_sqrt hradius_ne).differentiableAt.comp x
    differentiable_radiusSq.differentiableAt

/-- The actual vector kernel is Fréchet differentiable away from its pole. -/
theorem differentiableAt_bsVectorKernel_coord {x : Space} (hx : x ≠ 0)
    (j : Fin 3) :
    DifferentiableAt ℝ (fun y : Space => bsVectorKernel y j) x := by
  have hnorm := differentiableAt_officialEuclideanNorm hx
  have hnorm_ne : officialEuclideanNorm x ≠ 0 := by
    intro hn
    apply hx
    apply norm_eq_zero.mp
    have hle := norm_le_officialEuclideanNorm x
    rw [hn] at hle
    exact le_antisymm hle (norm_nonneg x)
  have hden : DifferentiableAt ℝ
      (fun y : Space => 4 * Real.pi * officialEuclideanNorm y ^ 3) x :=
    (differentiableAt_const (c := 4 * Real.pi)).mul (hnorm.pow 3)
  have hden_ne : 4 * Real.pi * officialEuclideanNorm x ^ 3 ≠ 0 := by
    positivity
  have hscalar : DifferentiableAt ℝ
      (fun y : Space => 1 / (4 * Real.pi * officialEuclideanNorm y ^ 3)) x :=
    by
      rw [show (fun y : Space =>
          1 / (4 * Real.pi * officialEuclideanNorm y ^ 3)) =
          (fun y : Space => 4 * Real.pi * officialEuclideanNorm y ^ 3)⁻¹ by
        funext y
        simp only [one_div, Pi.inv_apply]]
      exact hden.inv hden_ne
  have hexplicit : DifferentiableAt ℝ
      (fun y : Space =>
        (1 / (4 * Real.pi * officialEuclideanNorm y ^ 3)) * y j) x :=
    hscalar.mul (by fun_prop)
  have hlocal : ∀ᶠ y : Space in nhds x, y ≠ 0 :=
    continuousAt_id.eventually_ne hx
  have hsame : (fun y : Space => bsVectorKernel y j) =ᶠ[nhds x]
      (fun y => (1 / (4 * Real.pi * officialEuclideanNorm y ^ 3)) * y j) := by
    filter_upwards [hlocal] with y hy
    rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul,
      bsKernelScalar_apply_of_ne_zero hy]
  exact hexplicit.congr_of_eventuallyEq hsame

/-- The off-origin integration-by-parts theorem instantiated with the
canonical smooth exterior cutoff.  All support and differentiability inputs
are discharged here; the three hypotheses state only that the displayed
whole-space integrals exist. -/
theorem integral_smoothExteriorCutoff_ibp
    {φ : Space → ℝ} (ε : ℝ) (hε : 0 < ε) (i j : Fin 3)
    (hφdiff : Differentiable ℝ φ)
    (hintLeft : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
          φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hintRight : Integrable (fun x : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x))
    (hintProduct : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ * fun z : Space => bsVectorKernel z j) x)) :
    (∫ x : Space, smoothExteriorCutoff ε x *
      (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
        φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))) =
      -∫ x : Space,
        fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
          (φ * fun z : Space => bsVectorKernel z j) x := by
  apply Navier.Analysis.BealeKatoMajda.integral_bsGradKernel_testFactor_ibp_away
    i j (tsupport_smoothExteriorCutoff_away hε)
  · intro x _
    exact hφdiff x
  · intro x _
    exact differentiable_smoothExteriorCutoff ε x
  · intro x hx
    exact (hφdiff x).mul
      (differentiableAt_bsVectorKernel_coord
        (tsupport_smoothExteriorCutoff_away hε x hx) j)
  · exact hintLeft
  · exact hintRight
  · exact hintProduct

/-- Truncated derivative-side term for the smooth puncture. -/
def smoothPuncturedDerivativeIntegral (ε : ℝ) (i j : Fin 3)
    (φ : Space → ℝ) : ℝ :=
  ∫ x : Space, smoothExteriorCutoff ε x *
    (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)

/-- Truncated Calderón--Zygmund tensor term for the smooth puncture. -/
def smoothPuncturedGradientIntegral (ε : ℝ) (i j : Fin 3)
    (φ : Space → ℝ) : ℝ :=
  ∫ x : Space, smoothExteriorCutoff ε x *
    (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))

/-- The derivative layer of the smooth radial puncture. -/
def smoothPunctureFlux (ε : ℝ) (i j : Fin 3)
    (φ : Space → ℝ) : ℝ :=
  ∫ x : Space,
    fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
      (φ x * bsVectorKernel x j)

/-- Exact finite-radius identity for the smooth exterior puncture. -/
theorem smoothPunctured_biotSavart_identity
    {φ : Space → ℝ} (ε : ℝ) (hε : 0 < ε) (i j : Fin 3)
    (hφdiff : Differentiable ℝ φ)
    (hintDerivative : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)))
    (hintGradient : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hintFlux : Integrable (fun x : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
        (φ x * bsVectorKernel x j)))
    (hintProduct : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ * fun z : Space => bsVectorKernel z j) x)) :
    -smoothPuncturedDerivativeIntegral ε i j φ =
      smoothPuncturedGradientIntegral ε i j φ +
        smoothPunctureFlux ε i j φ := by
  have hpoint : ∀ x : Space,
      smoothExteriorCutoff ε x *
          (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
            φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)) =
        ((fun x => smoothExteriorCutoff ε x *
            (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)) +
          (fun x => smoothExteriorCutoff ε x *
            (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)))) x := by
    intro x
    simp only [Pi.add_apply]
    ring
  have hintLeft : Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
          φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))) :=
    (hintDerivative.add hintGradient).congr
      (ae_of_all _ fun x => (hpoint x).symm)
  have hibp := integral_smoothExteriorCutoff_ibp ε hε i j hφdiff
    hintLeft hintFlux hintProduct
  have hsplit : (∫ x : Space, smoothExteriorCutoff ε x *
      (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
        φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))) =
      (∫ x : Space, smoothExteriorCutoff ε x *
        (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)) +
      ∫ x : Space, smoothExteriorCutoff ε x *
        (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)) := by
    calc
      _ = ∫ x : Space,
          ((fun x => smoothExteriorCutoff ε x *
              (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)) +
            (fun x => smoothExteriorCutoff ε x *
              (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)))) x :=
        integral_congr_ae (ae_of_all _ hpoint)
      _ = _ := integral_add hintDerivative hintGradient
  rw [hsplit] at hibp
  simp only [Pi.mul_apply] at hibp
  change smoothPuncturedDerivativeIntegral ε i j φ +
      smoothPuncturedGradientIntegral ε i j φ =
        -smoothPunctureFlux ε i j φ at hibp
  linarith

/-- Pointwise formula for the smooth puncture flux. -/
theorem smoothPunctureFlux_eq (ε : ℝ) (i j : Fin 3) (φ : Space → ℝ) :
    smoothPunctureFlux ε i j φ =
      ∫ x : Space,
        (deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
          (2 * x i / ε ^ 2)) * (φ x * bsVectorKernel x j) := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smoothExteriorCutoff_fderiv_basis]

private abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

/-- Reflection of one Euclidean coordinate. -/
private def euclideanCoordinateFlip (k : Fin 3) :
    EuclideanThree ≃ₗᵢ[ℝ] EuclideanThree :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun l : Fin 3 => if l = k then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] private theorem euclideanCoordinateFlip_apply_same
    (k : Fin 3) (x : EuclideanThree) :
    euclideanCoordinateFlip k x k = -x k := by
  simp [euclideanCoordinateFlip]

@[simp] private theorem euclideanCoordinateFlip_apply_ne
    {k l : Fin 3} (h : l ≠ k) (x : EuclideanThree) :
    euclideanCoordinateFlip k x l = x l := by
  simp [euclideanCoordinateFlip, h]

/-- Reindexing Euclidean coordinates by a permutation. -/
private def euclideanCoordinatePerm (e : Equiv.Perm (Fin 3)) :
    EuclideanThree ≃ₗᵢ[ℝ] EuclideanThree :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

private theorem measurePreserving_euclideanCoordinateFlip (k : Fin 3) :
    MeasurePreserving (euclideanCoordinateFlip k) volume volume :=
  (euclideanCoordinateFlip k).measurePreserving

private theorem measurePreserving_euclideanCoordinatePerm
    (e : Equiv.Perm (Fin 3)) :
    MeasurePreserving (euclideanCoordinatePerm e) volume volume :=
  (euclideanCoordinatePerm e).measurePreserving

private theorem integral_radial_mul_coord_mul_coord_eq_zero
    (h : ℝ → ℝ) {i j : Fin 3} (hij : i ≠ j) :
    (∫ x : EuclideanThree, h ‖x‖ * x i * x j) = 0 := by
  let flip := euclideanCoordinateFlip i
  let g : EuclideanThree → ℝ := fun x => h ‖x‖ * x i * x j
  have hinv := (measurePreserving_euclideanCoordinateFlip i).integral_comp
    flip.toHomeomorph.measurableEmbedding g
  have hodd : (fun x => g (flip x)) = fun x => -g x := by
    funext x
    simp [g, flip, norm_map, euclideanCoordinateFlip_apply_ne hij.symm]
  rw [hodd, integral_neg] at hinv
  change -(∫ x : EuclideanThree, g x) = ∫ x : EuclideanThree, g x at hinv
  have : (∫ x : EuclideanThree, g x) = 0 := by linarith
  exact this

private theorem integral_radial_mul_coord_sq_eq
    (h : ℝ → ℝ) (i j : Fin 3) :
    (∫ x : EuclideanThree, h ‖x‖ * x i ^ 2) =
      ∫ x : EuclideanThree, h ‖x‖ * x j ^ 2 := by
  let swap := euclideanCoordinatePerm (Equiv.swap i j)
  let g : EuclideanThree → ℝ := fun x => h ‖x‖ * x j ^ 2
  have hinv := (measurePreserving_euclideanCoordinatePerm (Equiv.swap i j)).integral_comp
    swap.toHomeomorph.measurableEmbedding g
  have hswap : (fun x => g (swap x)) = fun x => h ‖x‖ * x i ^ 2 := by
    funext x
    simp [g, swap, euclideanCoordinatePerm, norm_map]
  rw [hswap] at hinv
  exact hinv

/-- Radial scalar multiplying `xᵢxⱼ` in the constant-test cutoff flux. -/
private def smoothFluxRadialWeight (ε r : ℝ) : ℝ :=
  deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) *
    (2 / ε ^ 2) * (1 / (4 * Real.pi * r ^ 3))

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have hs : DifferentiableAt ℝ Real.smoothTransition t := by
    have hs' : ContDiff ℝ 1 Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact (hs'.differentiable (by norm_num)) t
  have heq : Real.smoothTransition =ᶠ[nhds t] fun _ : ℝ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  have hz := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  exact hs.hasDerivAt.unique hz

private theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have hs : DifferentiableAt ℝ Real.smoothTransition t := by
    have hs' : ContDiff ℝ 1 Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact (hs'.differentiable (by norm_num)) t
  have heq : Real.smoothTransition =ᶠ[nhds t] fun _ : ℝ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  have hz := (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq
  exact hs.hasDerivAt.unique hz

private theorem continuous_deriv_smoothTransition :
    Continuous (deriv Real.smoothTransition) := by
  have hs : ContDiff ℝ 2 Real.smoothTransition :=
    Real.smoothTransition.contDiff
  exact hs.continuous_deriv (by norm_num)

private theorem continuous_euclideanFluxTensor (ε : ℝ) (hε : 0 < ε)
    (i j : Fin 3) :
    Continuous (fun y : EuclideanThree =>
      smoothFluxRadialWeight ε ‖y‖ * y i * y j) := by
  apply continuous_iff_continuousAt.2
  intro y
  by_cases hy : y = 0
  · subst y
    have hrad : 0 < ε := hε
    have hevent : ∀ᶠ z : EuclideanThree in nhds 0, ‖z‖ < ε := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanThree) hrad] with z hz
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzero : (fun z : EuclideanThree =>
        smoothFluxRadialWeight ε ‖z‖ * z i * z j) =ᶠ[nhds 0]
        fun _ => 0 := by
      filter_upwards [hevent] with z hz
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      have hq : ‖z‖ ^ 2 / ε ^ 2 - 1 < 0 := by
        rw [sub_lt_zero, div_lt_one hεsq]
        exact (sq_lt_sq₀ (norm_nonneg z) hε.le).2 hz
      rw [smoothFluxRadialWeight,
        deriv_smoothTransition_eq_zero_of_lt_zero hq]
      ring
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const hzero
  · have hnorm : ‖y‖ ≠ 0 := (norm_ne_zero_iff.mpr hy)
    unfold smoothFluxRadialWeight
    have hd : ContinuousAt
        (fun z : EuclideanThree =>
          deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1)) y :=
      continuous_deriv_smoothTransition.continuousAt.comp
        (by fun_prop)
    have hden : ContinuousAt
        (fun z : EuclideanThree => 4 * Real.pi * ‖z‖ ^ 3) y := by
      fun_prop
    have hden_ne : 4 * Real.pi * ‖y‖ ^ 3 ≠ 0 := by positivity
    fun_prop

private theorem hasCompactSupport_euclideanFluxTensor
    (ε : ℝ) (hε : 0 < ε) (i j : Fin 3) :
    HasCompactSupport (fun y : EuclideanThree =>
      smoothFluxRadialWeight ε ‖y‖ * y i * y j) := by
  let R : ℝ := Real.sqrt 2 * ε
  apply HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanThree) R)
  intro y hy
  have hynorm : R < ‖y‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hq : 1 < ‖y‖ ^ 2 / ε ^ 2 - 1 := by
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hy2raw : (Real.sqrt 2 * ε) ^ 2 < ‖y‖ ^ 2 :=
      (sq_lt_sq₀ (mul_nonneg hsqrt.le hε.le) (norm_nonneg y)).2 hynorm
    have hy2 : 2 * ε ^ 2 < ‖y‖ ^ 2 := by
      nlinarith
    rw [lt_sub_iff_add_lt]
    norm_num
    exact (lt_div_iff₀ hεsq).2 hy2
  rw [smoothFluxRadialWeight,
    deriv_smoothTransition_eq_zero_of_one_lt hq]
  ring

private theorem integrable_euclideanFluxTensor
    (ε : ℝ) (hε : 0 < ε) (i j : Fin 3) :
    Integrable (fun y : EuclideanThree =>
      smoothFluxRadialWeight ε ‖y‖ * y i * y j) :=
  (continuous_euclideanFluxTensor ε hε i j).integrable_of_hasCompactSupport
    (hasCompactSupport_euclideanFluxTensor ε hε i j)

private def spaceToEuclideanMeasurableEquiv : Space ≃ᵐ EuclideanThree :=
  MeasurableEquiv.mk (WithLp.equiv 2 Space).symm
    (by measurability)
    (by
      change Measurable (fun x : EuclideanThree => (fun i => x i : Space))
      fun_prop)

private theorem integral_space_comp_officialEuclideanPoint
    (g : EuclideanThree → ℝ) :
    (∫ x : Space, g (officialEuclideanPoint x)) =
      ∫ y : EuclideanThree, g y := by
  exact (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    spaceToEuclideanMeasurableEquiv.measurableEmbedding g

private theorem smoothPunctureFlux_one_eq_euclidean
    (ε : ℝ) (i j : Fin 3) :
    smoothPunctureFlux ε i j (fun _ => 1) =
      ∫ y : EuclideanThree, smoothFluxRadialWeight ε ‖y‖ * y i * y j := by
  rw [smoothPunctureFlux_eq]
  have hpoint : ∀ x : Space,
      (deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
          (2 * x i / ε ^ 2)) * ((1 : ℝ) * bsVectorKernel x j) =
        smoothFluxRadialWeight ε (officialEuclideanNorm x) * x i * x j := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [smoothFluxRadialWeight, bsVectorKernel, bsKernelScalar]
    · rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul,
        bsKernelScalar_apply_of_ne_zero hx,
        radiusSq_eq_officialEuclideanNorm_sq]
      unfold smoothFluxRadialWeight
      ring
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  let g : EuclideanThree → ℝ := fun y =>
    smoothFluxRadialWeight ε ‖y‖ * y i * y j
  have htransport := integral_space_comp_officialEuclideanPoint g
  simpa only [g, officialEuclideanNorm, officialEuclideanPoint_apply] using htransport

theorem smoothPunctureFlux_one_offDiag
    (ε : ℝ) {i j : Fin 3} (hij : i ≠ j) :
    smoothPunctureFlux ε i j (fun _ => 1) = 0 := by
  rw [smoothPunctureFlux_one_eq_euclidean]
  exact integral_radial_mul_coord_mul_coord_eq_zero _ hij

theorem smoothPunctureFlux_one_diagonal_eq
    (ε : ℝ) (i j : Fin 3) :
    smoothPunctureFlux ε i i (fun _ => 1) =
      smoothPunctureFlux ε j j (fun _ => 1) := by
  rw [smoothPunctureFlux_one_eq_euclidean,
    smoothPunctureFlux_one_eq_euclidean]
  calc
    (∫ y : EuclideanThree,
        smoothFluxRadialWeight ε ‖y‖ * y i * y i) =
        ∫ y : EuclideanThree,
          smoothFluxRadialWeight ε ‖y‖ * y i ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y : EuclideanThree,
        smoothFluxRadialWeight ε ‖y‖ * y j ^ 2 :=
      integral_radial_mul_coord_sq_eq _ i j
    _ = ∫ y : EuclideanThree,
        smoothFluxRadialWeight ε ‖y‖ * y j * y j := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private def smoothRadialProfile (ε r : ℝ) : ℝ :=
  Real.smoothTransition (r ^ 2 / ε ^ 2 - 1)

private theorem smoothRadialProfile_hasDerivAt (ε r : ℝ) :
    HasDerivAt (smoothRadialProfile ε)
      (deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) *
        (2 * r / ε ^ 2)) r := by
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 / ε ^ 2 - 1)
      (2 * r / ε ^ 2) r := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one] using
      ((hasDerivAt_id r).pow 2 |>.div_const (ε ^ 2) |>.sub_const 1)
  have hs' : ContDiff ℝ 1 Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hs : DifferentiableAt ℝ Real.smoothTransition
      (r ^ 2 / ε ^ 2 - 1) := (hs'.differentiable (by norm_num)) _
  exact hs.hasDerivAt.comp r hinner

private theorem integral_smoothRadialProfile_deriv_Ioi
    {ε : ℝ} (hε : 0 < ε) :
    (∫ r : ℝ in Ioi 0,
      deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) *
        (2 * r / ε ^ 2)) = 1 := by
  let R : ℝ := Real.sqrt 2 * ε
  let q : ℝ → ℝ := fun r =>
    deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) *
      (2 * r / ε ^ 2)
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg 2) hε.le
  have hcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hFTC : (∫ r : ℝ in (0 : ℝ)..R, q r) = 1 := by
    have hderiv : ∀ r ∈ uIcc (0 : ℝ) R,
        HasDerivAt (smoothRadialProfile ε) (q r) r := by
      intro r _
      simpa only [q] using smoothRadialProfile_hasDerivAt ε r
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 R)]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hεsq : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
    have hargR : R ^ 2 / ε ^ 2 - 1 = 1 := by
      dsimp only [R]
      field_simp
      nlinarith
    rw [smoothRadialProfile, hargR, Real.smoothTransition.one_of_one_le (by norm_num)]
    have harg0 : (0 : ℝ) ^ 2 / ε ^ 2 - 1 = -1 := by ring
    rw [smoothRadialProfile, harg0,
      Real.smoothTransition.zero_of_nonpos (by norm_num)]
    ring
  have hset : (∫ r : ℝ in Ioi 0, q r) = ∫ r : ℝ in Ioc 0 R, q r := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with r
    by_cases hrIoi : r ∈ Ioi (0 : ℝ)
    · by_cases hrR : r ≤ R
      · have hrIoc : r ∈ Ioc (0 : ℝ) R := ⟨hrIoi, hrR⟩
        simp [hrIoi, hrIoc]
      · have hrgt : R < r := lt_of_not_ge hrR
        have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
        have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        have hqarg : 1 < r ^ 2 / ε ^ 2 - 1 := by
          have hrnonneg : 0 ≤ r := hrIoi.le
          have hr2raw : R ^ 2 < r ^ 2 :=
            (sq_lt_sq₀ hR hrnonneg).2 hrgt
          have hr2 : 2 * ε ^ 2 < r ^ 2 := by
            dsimp only [R] at hr2raw
            nlinarith
          rw [lt_sub_iff_add_lt]
          norm_num
          exact (lt_div_iff₀ hεsq).2 hr2
        have hqzero : q r = 0 := by
          dsimp only [q]
          rw [deriv_smoothTransition_eq_zero_of_one_lt hqarg]
          ring
        have hrIoc : r ∉ Ioc (0 : ℝ) R := by simp [hrR]
        simp [hrIoi, hrIoc, hqzero]
    · have hrIoc : r ∉ Ioc (0 : ℝ) R := fun hr => hrIoi hr.1
      simp [hrIoi, hrIoc]
  rw [hset, ← intervalIntegral.integral_of_le hR]
  exact hFTC

private theorem euclideanThree_unitBall_volume :
    volume.real (Metric.ball (0 : EuclideanThree) 1) =
      4 * Real.pi / 3 := by
  change (volume (Metric.ball (0 : EuclideanThree) 1)).toReal = _
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have harg : ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 := by norm_num
  rw [harg]
  have hg := Real.Gamma_nat_add_half 2
  norm_num at hg
  rw [hg]
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

private theorem integral_euclideanFluxTrace
    {ε : ℝ} (hε : 0 < ε) :
    (∫ y : EuclideanThree,
      smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2) = 1 := by
  let f : ℝ → ℝ := fun r => smoothFluxRadialWeight ε r * r ^ 2
  have hrad := MeasureTheory.integral_fun_norm_addHaar
    (E := EuclideanThree) (F := ℝ) volume f
  have hdim : Module.finrank ℝ EuclideanThree = 3 := by
    simp [EuclideanThree]
  rw [hdim] at hrad
  have hrad' : (∫ y : EuclideanThree,
      smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2) =
      3 * volume.real (Metric.ball (0 : EuclideanThree) 1) *
        ∫ r : ℝ in Ioi 0,
          r ^ 2 * (smoothFluxRadialWeight ε r * r ^ 2) := by
    simpa [f, mul_assoc] using hrad
  rw [hrad', euclideanThree_unitBall_volume]
  have hradial : (∫ r : ℝ in Ioi 0,
      r ^ 2 * (smoothFluxRadialWeight ε r * r ^ 2)) =
      (1 / (4 * Real.pi)) *
        ∫ r : ℝ in Ioi 0,
          deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) *
            (2 * r / ε ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt hr
    unfold smoothFluxRadialWeight
    field_simp
  rw [hradial, integral_smoothRadialProfile_deriv_Ioi hε]
  field_simp [Real.pi_ne_zero]

theorem smoothPunctureFlux_one_trace
    {ε : ℝ} (hε : 0 < ε) :
    (∑ i : Fin 3, smoothPunctureFlux ε i i (fun _ => 1)) = 1 := by
  simp_rw [smoothPunctureFlux_one_eq_euclidean]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => integrable_euclideanFluxTensor ε hε i i)]
  calc
    (∫ y : EuclideanThree,
        ∑ i : Fin 3, smoothFluxRadialWeight ε ‖y‖ * y i * y i) =
        ∫ y : EuclideanThree,
          smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 1 := integral_euclideanFluxTrace hε

/-- The smooth radial cutoff carries exactly the isotropic one-third boundary
mass, at every positive radius. -/
theorem smoothPunctureFlux_one
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    smoothPunctureFlux ε i j (fun _ => 1) =
      (1 / 3 : ℝ) * basisVector i j := by
  by_cases hij : i = j
  · subst j
    have ht := smoothPunctureFlux_one_trace hε
    have hall : ∀ k : Fin 3,
        smoothPunctureFlux ε k k (fun _ => 1) =
          smoothPunctureFlux ε i i (fun _ => 1) := fun k =>
      smoothPunctureFlux_one_diagonal_eq ε k i
    simp_rw [hall] at ht
    simp only [Fin.sum_univ_three] at ht
    have hdiag : smoothPunctureFlux ε i i (fun _ => 1) = 1 / 3 := by
      linarith
    rw [hdiag]
    simp [basisVector]
  · rw [smoothPunctureFlux_one_offDiag ε hij]
    simp [basisVector, hij]

/-- The scalar tensor density integrated by `smoothPunctureFlux`. -/
private def smoothFluxTensor (ε : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  (deriv Real.smoothTransition (radiusSq x / ε ^ 2 - 1) *
    (2 * x i / ε ^ 2)) * bsVectorKernel x j

private theorem smoothFluxTensor_eq_euclidean
    (ε : ℝ) (i j : Fin 3) (x : Space) :
    smoothFluxTensor ε i j x =
      smoothFluxRadialWeight ε (officialEuclideanNorm x) * x i * x j := by
  by_cases hx : x = 0
  · subst x
    simp [smoothFluxTensor, smoothFluxRadialWeight, bsVectorKernel, bsKernelScalar]
  · rw [smoothFluxTensor, bsVectorKernel, Pi.smul_apply, smul_eq_mul,
      bsKernelScalar_apply_of_ne_zero hx,
      radiusSq_eq_officialEuclideanNorm_sq]
    unfold smoothFluxRadialWeight
    ring

private theorem integrable_smoothFluxTensor
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    Integrable (smoothFluxTensor ε i j) := by
  let g : EuclideanThree → ℝ := fun y =>
    smoothFluxRadialWeight ε ‖y‖ * y i * y j
  have hg : Integrable g := integrable_euclideanFluxTensor ε hε i j
  have hcomp : g ∘ officialEuclideanPoint = smoothFluxTensor ε i j := by
    funext x
    rw [smoothFluxTensor_eq_euclidean]
    rfl
  rw [← hcomp]
  exact ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    spaceToEuclideanMeasurableEquiv.measurableEmbedding).2 hg

/-- Positive radial trace density dominating every cutoff-flux tensor entry. -/
private def smoothFluxTraceDensity (ε : ℝ) (x : Space) : ℝ :=
  smoothFluxRadialWeight ε (officialEuclideanNorm x) *
    officialEuclideanNorm x ^ 2

private theorem smoothFluxRadialWeight_nonneg
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    0 ≤ smoothFluxRadialWeight ε r := by
  unfold smoothFluxRadialWeight
  have hd : 0 ≤ deriv Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) :=
    Real.smoothTransition.monotone.deriv_nonneg
  positivity

private theorem smoothFluxTraceDensity_nonneg
    {ε : ℝ} (hε : 0 < ε) (x : Space) :
    0 ≤ smoothFluxTraceDensity ε x := by
  exact mul_nonneg
    (smoothFluxRadialWeight_nonneg hε (officialEuclideanNorm_nonneg x))
    (sq_nonneg _)

private theorem integrable_smoothFluxTraceDensity
    {ε : ℝ} (hε : 0 < ε) : Integrable (smoothFluxTraceDensity ε) := by
  let g : EuclideanThree → ℝ := fun y =>
    smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2
  have hsum : Integrable (fun y : EuclideanThree =>
      ∑ i : Fin 3, smoothFluxRadialWeight ε ‖y‖ * y i * y i) :=
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun i _ => integrable_euclideanFluxTensor ε hε i i)
  have hg : Integrable g := hsum.congr (ae_of_all _ fun y => by
    dsimp only [g]
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring)
  have hcomp : g ∘ officialEuclideanPoint = smoothFluxTraceDensity ε := by
    funext x
    rfl
  rw [← hcomp]
  exact ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    spaceToEuclideanMeasurableEquiv.measurableEmbedding).2 hg

private theorem integral_smoothFluxTraceDensity
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : Space, smoothFluxTraceDensity ε x) = 1 := by
  let g : EuclideanThree → ℝ := fun y =>
    smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2
  have htransport := integral_space_comp_officialEuclideanPoint g
  change (∫ x : Space, g (officialEuclideanPoint x)) = _ at htransport
  rw [show (fun x : Space => g (officialEuclideanPoint x)) =
      smoothFluxTraceDensity ε by funext x; rfl] at htransport
  rw [htransport]
  exact integral_euclideanFluxTrace hε

private theorem abs_smoothFluxTensor_le_trace
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (x : Space) :
    |smoothFluxTensor ε i j x| ≤ smoothFluxTraceDensity ε x := by
  rw [smoothFluxTensor_eq_euclidean]
  let y : EuclideanThree := officialEuclideanPoint x
  have hw : 0 ≤ smoothFluxRadialWeight ε ‖y‖ :=
    smoothFluxRadialWeight_nonneg hε (norm_nonneg y)
  have hsum : ‖y‖ ^ 2 = ∑ k : Fin 3, (y k) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have hi : (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (y k)) (Finset.mem_univ i)
  have hj : (y j) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (y k)) (Finset.mem_univ j)
  have habs : |y i * y j| ≤ ‖y‖ ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_abs (y i), sq_abs (y j), norm_nonneg y,
      sq_nonneg (|y i| - |y j|)]
  change |smoothFluxRadialWeight ε ‖y‖ * y i * y j| ≤
    smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2
  rw [abs_mul, abs_mul, abs_of_nonneg hw]
  calc
    smoothFluxRadialWeight ε ‖y‖ * |y i| * |y j| =
        smoothFluxRadialWeight ε ‖y‖ * |y i * y j| := by
      rw [abs_mul]
      ring
    _ ≤ smoothFluxRadialWeight ε ‖y‖ * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_left habs hw

private theorem smoothFluxTensor_eq_zero_of_outer
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) {x : Space}
    (hx : Real.sqrt 2 * ε < officialEuclideanNorm x) :
    smoothFluxTensor ε i j x = 0 := by
  rw [smoothFluxTensor_eq_euclidean]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hx2raw : (Real.sqrt 2 * ε) ^ 2 < officialEuclideanNorm x ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg hsqrt.le hε.le)
      (officialEuclideanNorm_nonneg x)).2 hx
  have hx2 : 2 * ε ^ 2 < officialEuclideanNorm x ^ 2 := by
    nlinarith
  have hq : 1 < officialEuclideanNorm x ^ 2 / ε ^ 2 - 1 := by
    rw [lt_sub_iff_add_lt]
    norm_num
    exact (lt_div_iff₀ hεsq).2 hx2
  unfold smoothFluxRadialWeight
  rw [deriv_smoothTransition_eq_zero_of_one_lt hq]
  ring

theorem smoothPunctureFlux_eq_integral_tensor
    (ε : ℝ) (i j : Fin 3) (φ : Space → ℝ) :
    smoothPunctureFlux ε i j φ =
      ∫ x : Space, smoothFluxTensor ε i j x * φ x := by
  rw [smoothPunctureFlux_eq]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold smoothFluxTensor
  ring

/-- The smooth finite-radius flux converges to the same local tensor as the
spherical puncture boundary. -/
theorem tendsto_smoothPunctureFlux (i j : Fin 3) (φ : Space → ℝ)
    (hφ : Continuous φ) (C : ℝ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    Tendsto (fun ε : ℝ => smoothPunctureFlux ε i j φ)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / 3 : ℝ) * basisVector i j * φ 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hlocal⟩ :=
    (Metric.continuousAt_iff.mp
      (show ContinuousAt φ (0 : Space) from hφ.continuousAt))
      (η / 2) (by positivity)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have heps : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      ε < δ / Real.sqrt 2 :=
    (show ∀ᶠ ε : ℝ in nhds 0, ε < δ / Real.sqrt 2 from
      Iio_mem_nhds (div_pos hδ hsqrt)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, heps] with ε hεmem hεsmall
  have hε : 0 < ε := hεmem
  have ha : Integrable (smoothFluxTensor ε i j) :=
    integrable_smoothFluxTensor hε i j
  have haφ : Integrable (fun x : Space => smoothFluxTensor ε i j x * φ x) :=
    ha.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hφ_bound)
  have ha0 : Integrable (fun x : Space => smoothFluxTensor ε i j x * φ 0) :=
    ha.mul_const (φ 0)
  have hrewrite : smoothPunctureFlux ε i j φ -
        (1 / 3 : ℝ) * basisVector i j * φ 0 =
      ∫ x : Space, smoothFluxTensor ε i j x * (φ x - φ 0) := by
    rw [← smoothPunctureFlux_one hε i j,
      smoothPunctureFlux_eq_integral_tensor,
      smoothPunctureFlux_eq_integral_tensor,
      ← MeasureTheory.integral_mul_const]
    simp only [mul_one]
    rw [← integral_sub haφ ha0]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [Real.dist_eq, hrewrite]
  have htraceInt : Integrable (fun x : Space =>
      (η / 2) * smoothFluxTraceDensity ε x) :=
    (integrable_smoothFluxTraceDensity hε).const_mul (η / 2)
  calc
    |∫ x : Space, smoothFluxTensor ε i j x * (φ x - φ 0)| =
        ‖∫ x : Space, smoothFluxTensor ε i j x * (φ x - φ 0)‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ x : Space, (η / 2) * smoothFluxTraceDensity ε x := by
      apply MeasureTheory.norm_integral_le_of_norm_le htraceInt
      filter_upwards [] with x
      by_cases hxouter : Real.sqrt 2 * ε < officialEuclideanNorm x
      · rw [smoothFluxTensor_eq_zero_of_outer hε i j hxouter]
        simp only [zero_mul, norm_zero]
        exact mul_nonneg (by positivity) (smoothFluxTraceDensity_nonneg hε x)
      · have hxrad : officialEuclideanNorm x < δ := by
          have hscale : Real.sqrt 2 * ε < δ := by
            simpa only [mul_comm] using (lt_div_iff₀ hsqrt).1 hεsmall
          exact lt_of_le_of_lt (le_of_not_gt hxouter) hscale
        have hxdist : dist x 0 < δ := by
          rw [dist_zero_right]
          exact lt_of_le_of_lt (norm_le_officialEuclideanNorm x) hxrad
        have hφclose : ‖φ x - φ 0‖ < η / 2 := by
          simpa only [Real.dist_eq, Real.norm_eq_abs] using hlocal hxdist
        rw [norm_mul]
        calc
          ‖smoothFluxTensor ε i j x‖ * ‖φ x - φ 0‖ ≤
              smoothFluxTraceDensity ε x * ‖φ x - φ 0‖ :=
            mul_le_mul_of_nonneg_right
              (by simpa only [Real.norm_eq_abs] using
                abs_smoothFluxTensor_le_trace hε i j x)
              (norm_nonneg _)
          _ ≤ smoothFluxTraceDensity ε x * (η / 2) :=
            mul_le_mul_of_nonneg_left hφclose.le
              (smoothFluxTraceDensity_nonneg hε x)
          _ = (η / 2) * smoothFluxTraceDensity ε x := mul_comm _ _
    _ = η / 2 := by
      rw [MeasureTheory.integral_const_mul,
        integral_smoothFluxTraceDensity hε, mul_one]
    _ < η := by linarith

/-- The smooth cutoff layer and the spherical puncture boundary have the same
shrinking-radius distributional limit. -/
theorem tendsto_smoothPunctureFlux_sub_punctureBoundary
    (i j : Fin 3) (φ : Space → ℝ)
    (hφ : Continuous φ) (C : ℝ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    Tendsto (fun ε : ℝ =>
      smoothPunctureFlux ε i j φ - punctureBoundary ε i j φ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hsmooth := tendsto_smoothPunctureFlux i j φ hφ C hφ_bound
  have hsource : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 := inf_le_left
  have hboundary :=
    (tendsto_punctureBoundary i j φ hφ C hφ_bound).mono_left hsource
  have hsub := hsmooth.sub hboundary
  simpa using hsub

theorem tendsto_smoothPunctureFlux_sub_punctureBoundary_schwartz
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Tendsto (fun ε : ℝ =>
      smoothPunctureFlux ε i j φ - punctureBoundary ε i j φ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply tendsto_smoothPunctureFlux_sub_punctureBoundary i j φ φ.continuous
    ((SchwartzMap.seminorm ℝ 0 0) φ)
  intro x
  simpa using φ.norm_iteratedFDeriv_le_seminorm ℝ 0 x
end Navier.Analysis.BiotSavartFiniteRadius
