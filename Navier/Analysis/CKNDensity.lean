import Navier.Analysis.CKNMeasureTransport

/-!
# Critical CKN densities under parabolic scaling

This module defines the pointwise densities `|u|^3`, `|p|^(3/2)`, and their
sum using the official Euclidean norm on velocity.  It proves their exact
weight-three scaling laws and transports `IntegrableOn` across the backward
cylinders from `CKNCylinderGeometry`.

These are algebraic and measure-transport leaves only.  They do not construct
a suitable weak solution, prove a local energy inequality, control pressure,
or establish an epsilon-regularity or partial-regularity theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CKNCylinder

open Navier
open Navier.Analysis.Covariance
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-- The velocity part `|u|^3` of the CKN density. -/
def velocityCubicDensity (u : VelocityEvolution) (z : SpaceTime) : ℝ :=
  officialEuclideanNorm (u z.1 z.2) ^ 3

/-- The pressure part `|p|^(3/2)` of the CKN density. -/
def pressureThreeHalvesDensity
    (p : PressureEvolution) (z : SpaceTime) : ℝ :=
  |p z.1 z.2| ^ (3 / 2 : ℝ)

/-- The unnormalized pointwise CKN density `|u|^3 + |p|^(3/2)`. -/
def cknDensity
    (u : VelocityEvolution) (p : PressureEvolution) (z : SpaceTime) : ℝ :=
  velocityCubicDensity u z + pressureThreeHalvesDensity p z

/-- The velocity cubic density has parabolic weight three. -/
theorem velocityCubicDensity_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (z : SpaceTime) :
    velocityCubicDensity (parabolicScaledVelocity lambda u) z =
      lambda ^ 3 * velocityCubicDensity u (parabolicPointMap lambda z) := by
  simp only [velocityCubicDensity, parabolicScaledVelocity,
    parabolicPointMap, officialEuclideanNorm_smul,
    abs_of_pos hLambda, mul_pow]

/-- The positive square `λ²`, raised to `3/2`, is `λ³`. -/
theorem sq_rpow_three_halves
    (lambda : ℝ) (hLambda : 0 < lambda) :
    (lambda ^ 2) ^ (3 / 2 : ℝ) = lambda ^ 3 := by
  rw [← Real.rpow_natCast_mul hLambda.le 2 (3 / 2 : ℝ)]
  norm_num

/-- The pressure three-halves density has parabolic weight three. -/
theorem pressureThreeHalvesDensity_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (p : PressureEvolution) (z : SpaceTime) :
    pressureThreeHalvesDensity (parabolicScaledPressure lambda p) z =
      lambda ^ 3 *
        pressureThreeHalvesDensity p (parabolicPointMap lambda z) := by
  rw [pressureThreeHalvesDensity, parabolicScaledPressure,
    parabolicPointMap, abs_mul, abs_of_nonneg (sq_nonneg lambda),
    Real.mul_rpow (sq_nonneg lambda) (abs_nonneg _),
    sq_rpow_three_halves lambda hLambda]
  rfl

/-- The full unnormalized CKN density has parabolic weight three. -/
theorem cknDensity_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (p : PressureEvolution) (z : SpaceTime) :
    cknDensity (parabolicScaledVelocity lambda u)
        (parabolicScaledPressure lambda p) z =
      lambda ^ 3 * cknDensity u p (parabolicPointMap lambda z) := by
  simp only [cknDensity, velocityCubicDensity_parabolicScaled lambda hLambda,
    pressureThreeHalvesDensity_parabolicScaled lambda hLambda]
  ring

/-- Velocity cubic integrability is equivalent on corresponding backward
cylinders under positive parabolic scaling. -/
theorem velocityCubicIntegrableOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    IntegrableOn
        (velocityCubicDensity (parabolicScaledVelocity lambda u))
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume ↔
      IntegrableOn (velocityCubicDensity u)
        (backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r))
        spaceTimeVolume := by
  rw [show velocityCubicDensity (parabolicScaledVelocity lambda u) =
      fun z => lambda ^ 3 *
        velocityCubicDensity u (parabolicPointMap lambda z) by
    funext z
    exact velocityCubicDensity_parabolicScaled lambda hLambda u z]
  exact integrableOn_const_mul_comp_backwardEuclideanCylinder_iff
    lambda hLambda (lambda ^ 3) (pow_ne_zero 3 hLambda.ne')
    t₀ x₀ r hr (velocityCubicDensity u)

/-- Pressure three-halves integrability is equivalent on corresponding
backward cylinders under positive parabolic scaling. -/
theorem pressureThreeHalvesIntegrableOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (p : PressureEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    IntegrableOn
        (pressureThreeHalvesDensity (parabolicScaledPressure lambda p))
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume ↔
      IntegrableOn (pressureThreeHalvesDensity p)
        (backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r))
        spaceTimeVolume := by
  rw [show
      pressureThreeHalvesDensity (parabolicScaledPressure lambda p) =
        fun z => lambda ^ 3 *
          pressureThreeHalvesDensity p (parabolicPointMap lambda z) by
    funext z
    exact pressureThreeHalvesDensity_parabolicScaled lambda hLambda p z]
  exact integrableOn_const_mul_comp_backwardEuclideanCylinder_iff
    lambda hLambda (lambda ^ 3) (pow_ne_zero 3 hLambda.ne')
    t₀ x₀ r hr (pressureThreeHalvesDensity p)

/-- Full CKN-density integrability is equivalent on corresponding backward
cylinders under positive parabolic scaling. -/
theorem cknDensityIntegrableOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (p : PressureEvolution)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    IntegrableOn
        (cknDensity (parabolicScaledVelocity lambda u)
          (parabolicScaledPressure lambda p))
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume ↔
      IntegrableOn (cknDensity u p)
        (backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r))
        spaceTimeVolume := by
  rw [show cknDensity (parabolicScaledVelocity lambda u)
        (parabolicScaledPressure lambda p) =
      fun z => lambda ^ 3 *
        cknDensity u p (parabolicPointMap lambda z) by
    funext z
    exact cknDensity_parabolicScaled lambda hLambda u p z]
  exact integrableOn_const_mul_comp_backwardEuclideanCylinder_iff
    lambda hLambda (lambda ^ 3) (pow_ne_zero 3 hLambda.ne')
    t₀ x₀ r hr (cknDensity u p)

end Navier.Analysis.CKNCylinder
