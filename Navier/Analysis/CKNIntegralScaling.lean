import Navier.Analysis.CKNDensity

/-!
# Exact parabolic Jacobian and normalized CKN scaling

The spacetime map `(t,x) ↦ (λ²t,λx)` has determinant `λ⁵` in three spatial
dimensions.  This file computes that determinant inside Lean, identifies the
exact Haar-measure multiplier, proves the corresponding change-of-variables
formula on backward cylinders, and defines the normalized CKN functional

`r⁻² ∫_{Q_r(t₀,x₀)} (|u|³ + |p|^(3/2))`.

The normalized functional is exactly invariant under positive parabolic
scaling.  These are geometric and measure-theoretic identities only.  They do
not construct a suitable weak solution, prove a local energy inequality,
control pressure, or establish epsilon regularity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CKNCylinder

open Navier
open Navier.Analysis.Covariance

/-- The parabolic spacetime map has determinant `λ² * λ³ = λ⁵`. -/
theorem det_parabolicPointEquiv
    (lambda : ℝ) (hLambda : lambda ≠ 0) :
    LinearMap.det ((parabolicPointEquiv lambda hLambda :
      SpaceTime ≃L[ℝ] SpaceTime) : SpaceTime →ₗ[ℝ] SpaceTime) =
      lambda ^ 5 := by
  let et : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 (lambda ^ 2) (pow_ne_zero 2 hLambda))
  let ex : Space ≃L[ℝ] Space :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 lambda hLambda)
  have ht : ((et : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
      (lambda ^ 2) • LinearMap.id := by
    ext
    simp [et]
  have hx : ((ex : Space →L[ℝ] Space) : Space →ₗ[ℝ] Space) =
      lambda • LinearMap.id := by
    ext i
    simp [ex]
  change LinearMap.det (LinearMap.prodMap
    (((et : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))
    (((ex : Space →L[ℝ] Space) : Space →ₗ[ℝ] Space))) = lambda ^ 5
  rw [LinearMap.det_prodMap, ht, hx, LinearMap.det_smul,
    LinearMap.det_smul]
  norm_num
  ring

/-- Positive parabolic dilation pushes spacetime volume forward by the exact
factor `λ⁻⁵`. -/
theorem map_parabolicPointEquiv_spaceTimeVolume
    (lambda : ℝ) (hLambda : 0 < lambda) :
    Measure.map (parabolicPointEquiv lambda hLambda.ne')
        spaceTimeVolume =
      ENNReal.ofReal (lambda⁻¹ ^ 5) • spaceTimeVolume := by
  let e := parabolicPointEquiv lambda hLambda.ne'
  have hdet : LinearMap.det (e : SpaceTime →ₗ[ℝ] SpaceTime) ≠ 0 := by
    rw [show LinearMap.det (e : SpaceTime →ₗ[ℝ] SpaceTime) =
      lambda ^ 5 by exact det_parabolicPointEquiv lambda hLambda.ne']
    exact pow_ne_zero 5 hLambda.ne'
  calc
    Measure.map (parabolicPointEquiv lambda hLambda.ne')
        spaceTimeVolume =
      Measure.map (e : SpaceTime → SpaceTime) spaceTimeVolume := by rfl
    _ = ENNReal.ofReal |(LinearMap.det
        (e : SpaceTime →ₗ[ℝ] SpaceTime))⁻¹| • spaceTimeVolume :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar spaceTimeVolume hdet
    _ = ENNReal.ofReal (lambda⁻¹ ^ 5) • spaceTimeVolume := by
      rw [show LinearMap.det (e : SpaceTime →ₗ[ℝ] SpaceTime) =
        lambda ^ 5 by exact det_parabolicPointEquiv lambda hLambda.ne']
      congr 2
      rw [abs_of_pos (inv_pos.mpr (pow_pos hLambda 5))]
      ring

/-- Exact change of variables for a real-valued set integral under positive
parabolic scaling. -/
theorem setIntegral_comp_parabolicPointMap
    (lambda : ℝ) (hLambda : 0 < lambda)
    (g : SpaceTime → ℝ) (s : Set SpaceTime) :
    (∫ z in parabolicPointMap lambda ⁻¹' s,
        g (parabolicPointMap lambda z) ∂spaceTimeVolume) =
      lambda⁻¹ ^ 5 * ∫ z in s, g z ∂spaceTimeVolume := by
  let e := parabolicPointEquiv lambda hLambda.ne'
  have hchange :
      (∫ z in s, g z ∂Measure.map (e : SpaceTime → SpaceTime)
        spaceTimeVolume) =
      ∫ z in e ⁻¹' s, g (e z) ∂spaceTimeVolume :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map g s
  have hemap :
      Measure.map (e : SpaceTime → SpaceTime) spaceTimeVolume =
        ENNReal.ofReal (lambda⁻¹ ^ 5) • spaceTimeVolume :=
    map_parabolicPointEquiv_spaceTimeVolume lambda hLambda
  calc
    (∫ z in parabolicPointMap lambda ⁻¹' s,
        g (parabolicPointMap lambda z) ∂spaceTimeVolume) =
      ∫ z in e ⁻¹' s, g (e z) ∂spaceTimeVolume := by rfl
    _ = ∫ z in s, g z ∂Measure.map (e : SpaceTime → SpaceTime)
        spaceTimeVolume := hchange.symm
    _ = ∫ z in s, g z ∂(ENNReal.ofReal (lambda⁻¹ ^ 5) •
        spaceTimeVolume) := by rw [hemap]
    _ = lambda⁻¹ ^ 5 * ∫ z in s, g z ∂spaceTimeVolume := by
      rw [Measure.restrict_smul, integral_smul_measure]
      rw [ENNReal.toReal_ofReal]
      · rfl
      · positivity

/-- Exact change of variables on corresponding backward Euclidean
cylinders. -/
theorem setIntegral_comp_parabolicPointMap_backwardEuclideanCylinder
    (lambda : ℝ) (hLambda : 0 < lambda)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r)
    (g : SpaceTime → ℝ) :
    (∫ z in backwardEuclideanCylinder t₀ x₀ r,
        g (parabolicPointMap lambda z) ∂spaceTimeVolume) =
      lambda⁻¹ ^ 5 *
        ∫ z in backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r),
          g z ∂spaceTimeVolume := by
  rw [← parabolicPointMap_preimage_backwardEuclideanCylinder
    lambda hLambda t₀ x₀ r hr]
  exact setIntegral_comp_parabolicPointMap lambda hLambda g _

/-- The unnormalized CKN integral has parabolic weight `-2`. -/
theorem cknDensityIntegral_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (p : PressureEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    (∫ z in backwardEuclideanCylinder t₀ x₀ r,
        cknDensity (parabolicScaledVelocity lambda u)
          (parabolicScaledPressure lambda p) z ∂spaceTimeVolume) =
      lambda⁻¹ ^ 2 *
        ∫ z in backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r),
          cknDensity u p z ∂spaceTimeVolume := by
  rw [show cknDensity (parabolicScaledVelocity lambda u)
      (parabolicScaledPressure lambda p) =
    fun z => lambda ^ 3 * cknDensity u p (parabolicPointMap lambda z) by
      funext z
      exact cknDensity_parabolicScaled lambda hLambda u p z]
  rw [MeasureTheory.integral_const_mul]
  rw [setIntegral_comp_parabolicPointMap_backwardEuclideanCylinder
    lambda hLambda t₀ x₀ r hr]
  field_simp

/-- The normalized backward-cylinder CKN functional. -/
def normalizedCKNFunctional
    (u : VelocityEvolution) (p : PressureEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) : ℝ :=
  r⁻¹ ^ 2 *
    ∫ z in backwardEuclideanCylinder t₀ x₀ r,
      cknDensity u p z ∂spaceTimeVolume

/-- The normalized CKN functional is exactly invariant under positive
parabolic scaling, with the center and radius transported geometrically. -/
theorem normalizedCKNFunctional_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (p : PressureEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    normalizedCKNFunctional
        (parabolicScaledVelocity lambda u)
        (parabolicScaledPressure lambda p) t₀ x₀ r =
      normalizedCKNFunctional u p
        (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r) := by
  unfold normalizedCKNFunctional
  rw [cknDensityIntegral_parabolicScaled
    lambda hLambda u p t₀ x₀ r hr]
  field_simp

end Navier.Analysis.CKNCylinder
