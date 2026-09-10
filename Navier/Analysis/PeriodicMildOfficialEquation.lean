import Navier.Analysis.PeriodicMildTimeDerivativeReconstruction
import Navier.Analysis.PeriodicPressureEllipticGain

/-!
# The reconstructed periodic mild balance is the official PDE

This module identifies the three spatial Fourier fields in the positive-time
mild balance with the actual Frechet operators in `Navier.Problem`.  Together
with the existing strong time-derivative reconstruction, this removes the
remaining algebraic/reconstruction gap between the constructed mild trajectory
and the official periodic momentum equation at a positive time.

It does not provide the horizon-uniform bound needed to continue arbitrary
periodic data globally, nor joint smoothness at the initial time.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ContDiff
open Set

namespace Navier.Analysis.PeriodicMildOfficialEquation

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildSmoothBootstrap
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicMildTimeDerivativeReconstruction
open Navier.Analysis.PeriodicNonlinearFourierReconstruction
open Navier.Analysis.PeriodicPressureEllipticGain
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.PeriodicPressureSpatialSmoothReconstruction
open Navier.Analysis.PeriodicSpatialSmoothReconstruction

/-- The real part of the reconstructed complex transport term is exactly the
official Frechet convection operator when the physical coefficients satisfy
Fourier reality. -/
theorem re_complexPointwiseConvection_eq_convection
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hreal : LatticeAntiHermitian (A t))
    (hall : ∀ n : ℕ, LatticePolynomialMoment n (A t))
    (x : Space) (i : Fin 3) :
    (complexPointwiseConvection (physicalCarrier (A t)) x i).re =
      convection (physicalMildVelocity A) t x i := by
  have hphysicalReal : LatticeHermitian (physicalCarrier (A t)) :=
    latticeHermitian_physicalCarrier hreal
  have hsmooth : ContDiff ℝ ∞ (physicalMildVelocity A t) := by
    rw [physicalMildVelocity,
      reconstructedVelocity_eq_physicalFourierReconstruction]
    exact contDiff_physicalFourierReconstruction_of_allMoments
      (physicalCarrier (A t)) (fun n => latticePolynomialMoment_physicalCarrier
        n (A t) (hall n))
  rw [CoordinatePDEBridge.convection_eq_official_sum
    (physicalMildVelocity A) (hsmooth.differentiable (by simp) x) i]
  unfold complexPointwiseConvection
  change Complex.reCLM (∑ j : Fin 3,
    complexFourierReconstruction (physicalCarrier (A t)) x j *
      complexSpatialDerivativeCoordinate (physicalCarrier (A t)) x i j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hvalue := congrArg (fun z : ComplexE3 => z j)
    (complexOfReal_physicalFourierReconstruction hphysicalReal x)
  have hvalue' :
      complexFourierReconstruction (physicalCarrier (A t)) x j =
        (physicalMildVelocity A t x j : ℂ) := by
    symm
    simpa only [complexEuclideanPoint, complexOfReal,
      complexOfParts, Pi.zero_apply,
      Complex.ofReal_zero, mul_zero, add_zero, physicalMildVelocity,
      reconstructedVelocity_eq_physicalFourierReconstruction] using hvalue
  have hderiv := spatialPartial_physicalMildVelocity_eq A t x i j
  change CoordinatePDEBridge.spatialPartial j
      (fun y => physicalMildVelocity A t y i) x =
    (complexSpatialDerivativeCoordinate (physicalCarrier (A t)) x i j).re
    at hderiv
  change (complexFourierReconstruction (physicalCarrier (A t)) x j *
    complexSpatialDerivativeCoordinate (physicalCarrier (A t)) x i j).re = _
  rw [Complex.mul_re, hvalue']
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [complexSpatialDerivativeCoordinate] using
    congrArg (fun z => physicalMildVelocity A t x j * z) hderiv.symm

/-- A line derivative of one recovered-pressure Fourier mode. -/
theorem hasDerivAt_fixedTimePressureMode_line
    (A : ℝ → WeightedLatticeBanach) (t : ℝ) (m : LatticeMode)
    (x : Space) (j : Fin 3) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => fixedTimePhysicalPressureModeTerm A t m
        (x + r • basisVector j))
      (periodOneDerivative * (latticeFrequency m j : ℂ) *
        fixedTimePhysicalPressureModeTerm A t m
          (x + s • basisVector j)) s := by
  unfold fixedTimePhysicalPressureModeTerm
  simpa only [mul_assoc] using
    (hasDerivAt_latticeCharacter_line m x j s).mul_const
      (physicalPressureCoefficient A t m)

/-- First pressure moments justify differentiating the actual recovered
pressure series term by term along a coordinate line. -/
theorem spatialPartial_physicalMildPressure_eq
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hdiv : LatticeDivergenceFree (physicalCarrier (A t)))
    (hmoment : LatticePolynomialMoment 1 (physicalCarrier (A t)))
    (x : Space) (j : Fin 3) :
    CoordinatePDEBridge.spatialPartial j (physicalMildPressure A t) x =
      (complexPressureGradientReconstruction
        (physicalCarrier (A t)) x j).re := by
  let g : LatticeMode → ℝ → ℂ := fun m s =>
    fixedTimePhysicalPressureModeTerm A t m (x + s • basisVector j)
  let g' : LatticeMode → ℝ → ℂ := fun m s =>
    periodOneDerivative * (latticeFrequency m j : ℂ) * g m s
  have hp := summable_periodOnePressureCoefficient_polynomial_noLoss
    1 (by norm_num) (physicalCarrier (A t)) (physicalCarrier (A t))
    hdiv hmoment hmoment
  have hmajor : Summable fun m : LatticeMode =>
      ‖periodOneDerivative‖ *
        (latticeModeWeight m * ‖physicalPressureCoefficient A t m‖) :=
    by simpa only [Real.rpow_one, physicalPressureCoefficient] using
      hp.mul_left ‖periodOneDerivative‖
  have hcomplex : HasDerivAt
      (fun s : ℝ => ∑' m : LatticeMode, g m s)
      (∑' m : LatticeMode, g' m 0) 0 := by
    exact hasDerivAt_tsum (g := g) (g' := g') (y₀ := 0)
      hmajor
      (fun m s => hasDerivAt_fixedTimePressureMode_line A t m x j s)
      (fun m s => by
        dsimp [g', g, fixedTimePhysicalPressureModeTerm]
        rw [norm_mul, norm_mul, norm_mul, norm_latticeCharacter]
        simp only [one_mul]
        calc
          ‖periodOneDerivative‖ * ‖(latticeFrequency m j : ℂ)‖ *
                ‖physicalPressureCoefficient A t m‖ ≤
              ‖periodOneDerivative‖ * latticeModeWeight m *
                ‖physicalPressureCoefficient A t m‖ := by
            gcongr
            simpa only [Complex.norm_real] using
              norm_latticeFrequency_coordinate_le_weight m j
          _ = ‖periodOneDerivative‖ *
              (latticeModeWeight m * ‖physicalPressureCoefficient A t m‖) := by
            ring
      )
      (by
        have hzero := summable_periodOnePressureCoefficient_polynomial_noLoss
          0 (by norm_num) (physicalCarrier (A t)) (physicalCarrier (A t)) hdiv
          (latticePolynomialMoment_mono (u := physicalCarrier (A t))
            (hu := hmoment) (by norm_num))
          (latticePolynomialMoment_mono (u := physicalCarrier (A t))
            (hu := hmoment) (by norm_num))
        apply Summable.of_norm
        simpa only [g, fixedTimePhysicalPressureModeTerm, norm_mul,
          norm_latticeCharacter, one_mul, Real.rpow_zero, one_mul,
          physicalPressureCoefficient] using hzero
      ) 0
  have hreal : HasDerivAt
      (fun s : ℝ => (∑' m : LatticeMode, g m s).re)
      (∑' m : LatticeMode, g' m 0).re 0 := by
    simpa [Function.comp_def] using
      (Complex.reCLM.hasFDerivAt.comp 0 hcomplex.hasFDerivAt).hasDerivAt
  unfold CoordinatePDEBridge.spatialPartial
  have hline : HasLineDerivAt ℝ (physicalMildPressure A t)
      (∑' m : LatticeMode, g' m 0).re x (basisVector j) := by
    simpa [HasLineDerivAt, physicalMildPressure,
      physicalSpacetimePressureModeTerm, fixedTimePhysicalPressureModeTerm,
      g, g'] using hreal
  rw [hline.lineDeriv]
  unfold complexPressureGradientReconstruction
  unfold complexCoefficientSeriesCoordinate periodOneGradientCoefficient
  congr 1
  apply tsum_congr
  intro m
  unfold g' g fixedTimePhysicalPressureModeTerm
  simp only [zero_smul, add_zero, physicalPressureCoefficient]
  ring

/-- A second coordinate derivative of the actual physical Fourier series,
with termwise differentiation justified by the second polynomial moment. -/
theorem secondSpatialPartial_physicalMildVelocity_eq
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hmoment : LatticePolynomialMoment 2 (physicalCarrier (A t)))
    (x : Space) (i j : Fin 3) :
    CoordinatePDEBridge.spatialPartial j
        (fun y => CoordinatePDEBridge.spatialPartial j
          (fun z => physicalMildVelocity A t z i) y) x =
      (∑' m : LatticeMode,
        (periodOneDerivative * (latticeFrequency m j : ℂ)) ^ 2 *
          latticeCharacter m x *
            weightedLatticeCoefficient (physicalCarrier (A t)) m i).re := by
  let g : LatticeMode → ℝ → ℂ := fun m s =>
    periodOneDerivative * (latticeFrequency m j : ℂ) *
      latticeCharacter m (x + s • basisVector j) *
        weightedLatticeCoefficient (physicalCarrier (A t)) m i
  let g' : LatticeMode → ℝ → ℂ := fun m s =>
    (periodOneDerivative * (latticeFrequency m j : ℂ)) ^ 2 *
      latticeCharacter m (x + s • basisVector j) *
        weightedLatticeCoefficient (physicalCarrier (A t)) m i
  have hmajor : Summable fun m : LatticeMode =>
      ‖periodOneDerivative‖ ^ 2 *
        polynomialMomentAmplitude 2 (physicalCarrier (A t)) m :=
    hmoment.mul_left (‖periodOneDerivative‖ ^ 2)
  have hinit : Summable fun m : LatticeMode => g m 0 := by
    apply Summable.of_norm
    have hone : LatticePolynomialMoment 1 (physicalCarrier (A t)) :=
      latticePolynomialMoment_mono (u := physicalCarrier (A t))
        (hu := hmoment) (by norm_num)
    have hs := hone.mul_left ‖periodOneDerivative‖
    apply hs.of_nonneg_of_le
    · intro m
      exact norm_nonneg _
    · intro m
      dsimp [g]
      rw [norm_mul, norm_mul, norm_mul, norm_latticeCharacter, mul_one]
      have hk : ‖(latticeFrequency m j : ℂ)‖ ≤ latticeModeWeight m := by
        simpa only [Complex.norm_real] using
          norm_latticeFrequency_coordinate_le_weight m j
      have hi : ‖weightedLatticeCoefficient (physicalCarrier (A t)) m i‖ ≤
          complexEuclideanNorm
            (weightedLatticeCoefficient (physicalCarrier (A t)) m) := by
        simpa [complexEuclideanNorm, complexEuclideanPoint] using
          PiLp.norm_apply_le (complexEuclideanPoint
            (weightedLatticeCoefficient (physicalCarrier (A t)) m)) i
      unfold polynomialMomentAmplitude
      rw [Real.rpow_one]
      calc
        ‖periodOneDerivative‖ * ‖(latticeFrequency m j : ℂ)‖ *
              ‖weightedLatticeCoefficient (physicalCarrier (A t)) m i‖ ≤
            ‖periodOneDerivative‖ * latticeModeWeight m *
              complexEuclideanNorm
                (weightedLatticeCoefficient (physicalCarrier (A t)) m) := by
          gcongr
          exact mul_nonneg (norm_nonneg _)
            (zero_le_one.trans (one_le_latticeModeWeight m))
        _ = ‖periodOneDerivative‖ *
            (latticeModeWeight m * complexEuclideanNorm
              (weightedLatticeCoefficient (physicalCarrier (A t)) m)) := by
          ring
  have hcomplex : HasDerivAt
      (fun s : ℝ => ∑' m : LatticeMode, g m s)
      (∑' m : LatticeMode, g' m 0) 0 := by
    exact hasDerivAt_tsum (g := g) (g' := g') (y₀ := 0)
      hmajor
      (fun m s => by
        dsimp [g, g']
        have h := (hasDerivAt_latticeCharacter_line m x j s).const_mul
          (periodOneDerivative * (latticeFrequency m j : ℂ))
        simpa only [pow_two, mul_assoc] using h.mul_const
          (weightedLatticeCoefficient (physicalCarrier (A t)) m i))
      (fun m s => by
        dsimp [g']
        rw [norm_mul, norm_mul, norm_pow, norm_mul,
          norm_latticeCharacter, mul_one]
        have hk : ‖(latticeFrequency m j : ℂ)‖ ≤ latticeModeWeight m := by
          simpa only [Complex.norm_real] using
            norm_latticeFrequency_coordinate_le_weight m j
        have hi : ‖weightedLatticeCoefficient (physicalCarrier (A t)) m i‖ ≤
            complexEuclideanNorm
              (weightedLatticeCoefficient (physicalCarrier (A t)) m) := by
          simpa [complexEuclideanNorm, complexEuclideanPoint] using
            PiLp.norm_apply_le (complexEuclideanPoint
              (weightedLatticeCoefficient (physicalCarrier (A t)) m)) i
        unfold polynomialMomentAmplitude
        calc
          (‖periodOneDerivative‖ * ‖(latticeFrequency m j : ℂ)‖) ^ 2 *
                ‖weightedLatticeCoefficient (physicalCarrier (A t)) m i‖ ≤
              (‖periodOneDerivative‖ * latticeModeWeight m) ^ 2 *
                complexEuclideanNorm
                  (weightedLatticeCoefficient (physicalCarrier (A t)) m) := by
            gcongr
          _ = ‖periodOneDerivative‖ ^ 2 *
              (latticeModeWeight m ^ (2 : ℝ) * complexEuclideanNorm
                (weightedLatticeCoefficient (physicalCarrier (A t)) m)) := by
            have hw : latticeModeWeight m ^ (2 : ℝ) =
                latticeModeWeight m ^ (2 : ℕ) := by
              exact Real.rpow_two _
            rw [hw]
            ring)
      hinit 0
  have hreal : HasDerivAt
      (fun s : ℝ => (∑' m : LatticeMode, g m s).re)
      (∑' m : LatticeMode, g' m 0).re 0 := by
    simpa [Function.comp_def] using
      (Complex.reCLM.hasFDerivAt.comp 0 hcomplex.hasFDerivAt).hasDerivAt
  have heq : (fun y => CoordinatePDEBridge.spatialPartial j
      (fun z => physicalMildVelocity A t z i) y) =
      fun y => (complexSpatialDerivativeCoordinate
        (physicalCarrier (A t)) y i j).re := by
    funext y
    exact spatialPartial_physicalMildVelocity_eq A t y i j
  rw [heq]
  unfold CoordinatePDEBridge.spatialPartial
  have hline : HasLineDerivAt ℝ
      (fun y => (complexSpatialDerivativeCoordinate
        (physicalCarrier (A t)) y i j).re)
      (∑' m : LatticeMode, g' m 0).re x (basisVector j) := by
    simpa [HasLineDerivAt, complexSpatialDerivativeCoordinate, g, g'] using hreal
  simpa only [g', zero_smul, add_zero] using hline.lineDeriv

theorem summable_secondSpatialFourierCoordinate
    (u : WeightedLatticeBanach)
    (hmoment : LatticePolynomialMoment 2 u)
    (x : Space) (i j : Fin 3) :
    Summable fun m : LatticeMode =>
      (periodOneDerivative * (latticeFrequency m j : ℂ)) ^ 2 *
        latticeCharacter m x * weightedLatticeCoefficient u m i := by
  apply Summable.of_norm
  have hs := hmoment.mul_left (‖periodOneDerivative‖ ^ 2)
  apply hs.of_nonneg_of_le
  · intro m
    exact norm_nonneg _
  · intro m
    rw [norm_mul, norm_mul, norm_pow, norm_mul,
      norm_latticeCharacter, mul_one]
    have hk : ‖(latticeFrequency m j : ℂ)‖ ≤ latticeModeWeight m := by
      simpa only [Complex.norm_real] using
        norm_latticeFrequency_coordinate_le_weight m j
    have hi : ‖weightedLatticeCoefficient u m i‖ ≤
        complexEuclideanNorm (weightedLatticeCoefficient u m) := by
      simpa [complexEuclideanNorm, complexEuclideanPoint] using
        PiLp.norm_apply_le
          (complexEuclideanPoint (weightedLatticeCoefficient u m)) i
    unfold polynomialMomentAmplitude
    have hw : latticeModeWeight m ^ (2 : ℝ) =
        latticeModeWeight m ^ (2 : ℕ) := Real.rpow_two _
    rw [hw]
    calc
      (‖periodOneDerivative‖ * ‖(latticeFrequency m j : ℂ)‖) ^ 2 *
            ‖weightedLatticeCoefficient u m i‖ ≤
          (‖periodOneDerivative‖ * latticeModeWeight m) ^ 2 *
            complexEuclideanNorm (weightedLatticeCoefficient u m) := by
        gcongr
      _ = ‖periodOneDerivative‖ ^ 2 *
          (latticeModeWeight m ^ 2 *
            complexEuclideanNorm (weightedLatticeCoefficient u m)) := by
        ring

/-- The positive Fourier viscous coefficient used in the mild balance is
exactly minus `ν` times the official componentwise Laplacian. -/
theorem re_viscousFourierSeries_eq_neg_mul_laplacian
    (ν : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hall : ∀ n : ℕ, LatticePolynomialMoment n (A t))
    (x : Space) (i : Fin 3) :
    (complexCoefficientSeriesCoordinate
      (fun k => periodOneViscousCoefficient ν k
        (weightedLatticeCoefficient (physicalCarrier (A t)) k)) x i).re =
      -ν * laplacian (physicalMildVelocity A) t x i := by
  have hallPhysical : ∀ n : ℕ,
      LatticePolynomialMoment n (physicalCarrier (A t)) := fun n =>
    latticePolynomialMoment_physicalCarrier n (A t) (hall n)
  have hsmooth : ContDiff ℝ ∞ (physicalMildVelocity A t) := by
    rw [physicalMildVelocity,
      reconstructedVelocity_eq_physicalFourierReconstruction]
    exact contDiff_physicalFourierReconstruction_of_allMoments
      (physicalCarrier (A t)) hallPhysical
  let q : Fin 3 → LatticeMode → ℂ := fun j m =>
    (periodOneDerivative * (latticeFrequency m j : ℂ)) ^ 2 *
      latticeCharacter m x *
        weightedLatticeCoefficient (physicalCarrier (A t)) m i
  have hq (j : Fin 3) : Summable (q j) := by
    simpa only [q] using summable_secondSpatialFourierCoordinate
      (physicalCarrier (A t)) (hallPhysical 2) x i j
  have hinterchange :
      (∑' m : LatticeMode, ∑ j : Fin 3, q j m) =
        ∑ j : Fin 3, ∑' m : LatticeMode, q j m := by
    simpa using Summable.tsum_finsetSum (s := Finset.univ)
      (fun j _hj => hq j)
  have hmode (m : LatticeMode) :
      latticeCharacter m x *
          periodOneViscousCoefficient ν m
            (weightedLatticeCoefficient (physicalCarrier (A t)) m) i =
        -(ν : ℂ) * ∑ j : Fin 3, q j m := by
    have hdot :
        ((latticeFrequency m ⬝ᵥ latticeFrequency m : ℝ) : ℂ) =
          ∑ j : Fin 3, (latticeFrequency m j : ℂ) ^ 2 := by
      simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    unfold q periodOneViscousCoefficient periodOneDerivative
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hdot]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcomplex :
      complexCoefficientSeriesCoordinate
          (fun k => periodOneViscousCoefficient ν k
            (weightedLatticeCoefficient (physicalCarrier (A t)) k)) x i =
        -(ν : ℂ) * ∑ j : Fin 3, ∑' m : LatticeMode, q j m := by
    unfold complexCoefficientSeriesCoordinate
    rw [← hinterchange, ← tsum_mul_left]
    apply tsum_congr
    exact hmode
  rw [hcomplex]
  have hre (z : ℂ) : (-(ν : ℂ) * z).re = -ν * z.re := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero]
    ring
  rw [hre]
  change -ν * Complex.reCLM
      (∑ j : Fin 3, ∑' m : LatticeMode, q j m) = _
  rw [map_sum]
  rw [CoordinatePDEBridge.laplacian_eq_official_sum
    (physicalMildVelocity A) hsmooth i]
  apply congrArg (fun z : ℝ => -ν * z)
  apply Finset.sum_congr rfl
  intro j _hj
  rw [secondSpatialPartial_physicalMildVelocity_eq A t
    (hallPhysical 2) x i j]
  rfl

/-- The real recovered pressure-gradient Fourier field is the official
Frechet pressure gradient. -/
theorem re_complexPressureGradientReconstruction_eq_pressureGradient
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hdiv : LatticeDivergenceFree (physicalCarrier (A t)))
    (hall : ∀ n : ℕ,
      LatticePolynomialMoment n (physicalCarrier (A t)))
    (x : Space) (i : Fin 3) :
    (complexPressureGradientReconstruction
        (physicalCarrier (A t)) x i).re =
      pressureGradient (physicalMildPressure A) t x i := by
  have hp : ContDiff ℝ ∞ (physicalMildPressure A t) :=
    contDiff_physicalMildPressure_at_fixedTime_noLoss A t hdiv hall
  rw [CoordinatePDEBridge.pressureGradient_eq_official
    (physicalMildPressure A) (hp.differentiable (by simp) x) i]
  have hmoment : LatticePolynomialMoment 1 (physicalCarrier (A t)) := by
    simpa using hall 1
  exact (spatialPartial_physicalMildPressure_eq A t hdiv hmoment x i).symm

/-- An actual bounded mild fixed point satisfies the repository's exact
Frechet momentum equation at every strictly positive interior time.  Every
Fourier balance, time derivative, spatial derivative, and pressure term below
is constructed from the trajectory; the caller supplies no PDE equality or
regularity conclusion. -/
theorem mildFixedPoint_officialMomentum_at
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, LatticeAntiHermitian (A s))
    {R a T t : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage (rawMildViscosity ν)
        (by unfold rawMildViscosity; positivity) u₀ A hdiv s hs.1)
    (ht : t ∈ Ioo a T) (x : Space) :
    timeDerivative (physicalMildVelocity A) t x +
        convection (physicalMildVelocity A) t x =
      ν • laplacian (physicalMildVelocity A) t x -
        pressureGradient (physicalMildPressure A) t x := by
  have hμ : 0 < rawMildViscosity ν := by
    unfold rawMildViscosity
    positivity
  have ht0 : 0 < t := ha.trans ht.1
  obtain ⟨B, _hB, hall⟩ :=
    exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
      (rawMildViscosity ν) hμ u₀ hu₀ A hAc hdiv hR ha haT.le
      hbound hmild
  have hallNat : ∀ n : ℕ, LatticePolynomialMoment n (A t) := by
    intro n
    have hhigh := (hall (2 * n) t ⟨ht.1.le, ht.2.le⟩).1
    exact latticePolynomialMoment_mono (u := A t) (hu := hhigh) (by
      rw [iteratedHalfOrder_eq]
      push_cast
      linarith [show (0 : ℝ) ≤ n by positivity])
  have hboot := mildFixedPoint_firstJointBootstrap_at
    ν hν u₀ hu₀ A hAc hdiv hR ⟨ht0, ht.2⟩ hbound hmild
  have hbalance (i : Fin 3) :=
    physicalLocalEvolution_pointwiseFourierBalance ν A t
      hboot.1 hboot.2.2.1 hboot.2.2.2.2 x i
  have htime (i : Fin 3) :=
    physicalPointwiseFourierBalance_to_officialTimeDerivative
      ν hν u₀ hu₀ A hAc hdiv hR ha haT hbound hmild ht x i
        (hbalance i)
  ext i
  have hconv := re_complexPointwiseConvection_eq_convection
    A t (hreal t) hallNat x i
  have hvisc := re_viscousFourierSeries_eq_neg_mul_laplacian
    ν A t hallNat x i
  have hdivPhysical :
      LatticeDivergenceFree (physicalCarrier (A t)) :=
    latticeDivergenceFree_physicalCarrier (hdiv t)
  have hallPhysical : ∀ n : ℕ,
      LatticePolynomialMoment n (physicalCarrier (A t)) := fun n =>
    latticePolynomialMoment_physicalCarrier n (A t) (hallNat n)
  have hpressure :=
    re_complexPressureGradientReconstruction_eq_pressureGradient
      A t hdivPhysical hallPhysical x i
  have heq := htime i
  rw [hconv, hvisc, hpressure] at heq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Cutoff-free positive-time form of the official momentum equation on the
whole local mild chart. -/
theorem mildFixedPoint_officialMomentum_positiveTime
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, LatticeAntiHermitian (A s))
    {R T t : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage (rawMildViscosity ν)
        (by unfold rawMildViscosity; positivity) u₀ A hdiv s hs.1)
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    timeDerivative (physicalMildVelocity A) t x +
        convection (physicalMildVelocity A) t x =
      ν • laplacian (physicalMildVelocity A) t x -
        pressureGradient (physicalMildPressure A) t x := by
  have ha : 0 < t / 2 := div_pos ht.1 (by norm_num)
  have hat : t / 2 < t := by linarith
  exact mildFixedPoint_officialMomentum_at
    ν hν u₀ hu₀ A hAc hdiv hreal hR
      ha (hat.trans ht.2) hbound hmild ⟨hat, ht.2⟩ x

end Navier.Analysis.PeriodicMildOfficialEquation

#print axioms Navier.Analysis.PeriodicMildOfficialEquation.re_complexPointwiseConvection_eq_convection
#print axioms Navier.Analysis.PeriodicMildOfficialEquation.spatialPartial_physicalMildPressure_eq
#print axioms Navier.Analysis.PeriodicMildOfficialEquation.secondSpatialPartial_physicalMildVelocity_eq
#print axioms Navier.Analysis.PeriodicMildOfficialEquation.re_viscousFourierSeries_eq_neg_mul_laplacian
#print axioms Navier.Analysis.PeriodicMildOfficialEquation.re_complexPressureGradientReconstruction_eq_pressureGradient
#print axioms Navier.Analysis.PeriodicMildOfficialEquation.mildFixedPoint_officialMomentum_positiveTime
