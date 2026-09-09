import Navier.Analysis.CriticalMildLocalUniformBootstrap
import Navier.Analysis.CriticalMildPolynomialMomentConvolution

/-!
# Higher uniform moments for the actual critical mild trajectory

This module starts the spatial induction above the uniform two-weight rung.
The scalar lemma below records the integrable three-half-frequency heat gain
used on a restarted nonlinear forcing.  The polynomial-moment convolution
layer supplies the complementary loss of one spatial weight.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildHigherUniformMoments

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHigherMomentBootstrap
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildAsymmetricPairSummable
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatCarrierAlgebra
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildLocalUniformBootstrap

/-- A three-half-frequency Gaussian gain obtained by splitting the heat time
equally between the full- and half-frequency elementary estimates. -/
theorem threeHalf_mul_exp_neg_mul_sq_le
    {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    q * Real.sqrt q * Real.exp (-(a * q * q)) ≤
      (Real.sqrt (a / 2))⁻¹ *
        (Real.sqrt (Real.sqrt (a / 2)))⁻¹ := by
  have ha2 : 0 < a / 2 := by positivity
  have hone := mul_exp_neg_mul_sq_le_inv_sqrt (a := a / 2) (r := q) ha2
  have hhalf := sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
    (a := a / 2) (q := q) ha2 hq
  have hexp : Real.exp (-(a * q * q)) =
      Real.exp (-((a / 2) * q * q)) *
        Real.exp (-((a / 2) * q * q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    q * Real.sqrt q * Real.exp (-(a * q * q)) =
        (q * Real.exp (-((a / 2) * q * q))) *
          (Real.sqrt q * Real.exp (-((a / 2) * q * q))) := by
      rw [hexp]
      ring
    _ ≤ (Real.sqrt (a / 2))⁻¹ *
        (Real.sqrt (Real.sqrt (a / 2)))⁻¹ := by
      exact mul_le_mul hone hhalf
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.exp_pos _).le)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Faithful inhomogeneous version of the three-half-frequency Gaussian
gain.  The four terms are the zero-, half-, one-, and three-half-frequency
pieces of `(1 + q)^(3/2)`.  Every time singularity displayed here is locally
integrable at zero. -/
theorem one_add_rpow_threeHalves_mul_exp_neg_mul_sq_le
    {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    (1 + q) ^ (3 / 2 : ℝ) * Real.exp (-(a * q * q)) ≤
      1 + (Real.sqrt a)⁻¹ + (Real.sqrt (Real.sqrt a))⁻¹ +
        (Real.sqrt (a / 2))⁻¹ *
          (Real.sqrt (Real.sqrt (a / 2)))⁻¹ := by
  have ha0 : 0 ≤ a := ha.le
  have hdec0 : 0 ≤ Real.exp (-(a * q * q)) := (Real.exp_pos _).le
  have hdec1 : Real.exp (-(a * q * q)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg ha0 (mul_nonneg hq hq)]
  have hsqrt : Real.sqrt (1 + q) ≤ 1 + Real.sqrt q := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  have hrewrite : (1 + q) ^ (3 / 2 : ℝ) =
      (1 + q) * Real.sqrt (1 + q) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one, Real.sqrt_eq_rpow]
  have hone := mul_exp_neg_mul_sq_le_inv_sqrt (a := a) (r := q) ha
  have hhalf := sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
    (a := a) (q := q) ha hq
  have hthree := threeHalf_mul_exp_neg_mul_sq_le ha hq
  rw [hrewrite]
  calc
    (1 + q) * Real.sqrt (1 + q) * Real.exp (-(a * q * q)) ≤
        (1 + q) * (1 + Real.sqrt q) * Real.exp (-(a * q * q)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hdec0
    _ = Real.exp (-(a * q * q)) +
          q * Real.exp (-(a * q * q)) +
          Real.sqrt q * Real.exp (-(a * q * q)) +
          (q * Real.sqrt q * Real.exp (-(a * q * q))) := by ring
    _ ≤ 1 + (Real.sqrt a)⁻¹ + (Real.sqrt (Real.sqrt a))⁻¹ +
          (Real.sqrt (a / 2))⁻¹ *
            (Real.sqrt (Real.sqrt (a / 2)))⁻¹ := by
      linarith

/-- The singular part of the three-half-frequency heat gain is exactly the
integrable exponent `r⁻³ᐟ⁴`. -/
theorem inv_sqrt_mul_inv_fourthRoot_eq_rpow_neg_three_fourths
    {r : ℝ} (hr : 0 < r) :
    (Real.sqrt r)⁻¹ * (Real.sqrt (Real.sqrt r))⁻¹ =
      r ^ (-(3 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hr.le, ← Real.rpow_neg_one,
    ← Real.rpow_mul hr.le, ← Real.rpow_neg_one,
    ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  norm_num

/-- The three-half-frequency heat kernel with viscosity `ν` is a constant
multiple of the integrable `r⁻³ᐟ⁴` time kernel. -/
theorem threeHalf_heatGainKernel_eq
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    (Real.sqrt ((ν * r) / 2))⁻¹ *
        (Real.sqrt (Real.sqrt ((ν * r) / 2)))⁻¹ =
      ((Real.sqrt (ν / 2))⁻¹ *
        (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) *
          r ^ (-(3 / 4 : ℝ)) := by
  have hν2 : 0 < ν / 2 := by positivity
  have hsqrt : Real.sqrt ((ν * r) / 2) =
      Real.sqrt (ν / 2) * Real.sqrt r := by
    rw [show ν * r / 2 = (ν / 2) * r by ring,
      Real.sqrt_mul hν2.le]
  have hfourth : Real.sqrt (Real.sqrt ((ν * r) / 2)) =
      Real.sqrt (Real.sqrt (ν / 2)) *
        Real.sqrt (Real.sqrt r) := by
    rw [hsqrt, Real.sqrt_mul (Real.sqrt_nonneg (ν / 2))]
  rw [hfourth, hsqrt, mul_inv_rev, mul_inv_rev]
  calc
    (Real.sqrt r)⁻¹ * (Real.sqrt (ν / 2))⁻¹ *
          ((Real.sqrt (Real.sqrt r))⁻¹ *
            (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) =
        ((Real.sqrt (ν / 2))⁻¹ *
          (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) *
            ((Real.sqrt r)⁻¹ *
              (Real.sqrt (Real.sqrt r))⁻¹) := by ring
    _ = ((Real.sqrt (ν / 2))⁻¹ *
          (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) *
            r ^ (-(3 / 4 : ℝ)) := by
      rw [inv_sqrt_mul_inv_fourthRoot_eq_rpow_neg_three_fourths hr]

/-- The `r⁻³ᐟ⁴` heat-gain kernel is interval-integrable up to the Duhamel
endpoint. -/
theorem intervalIntegrable_threeHalf_heatGainKernel
    (ν : ℝ) (hν : 0 < ν) {b t : ℝ} (hbt : b ≤ t) :
    IntervalIntegrable
      (fun s : ℝ =>
        (Real.sqrt ((ν * (t - s)) / 2))⁻¹ *
          (Real.sqrt (Real.sqrt ((ν * (t - s)) / 2)))⁻¹)
      volume b t := by
  let C : ℝ := (Real.sqrt (ν / 2))⁻¹ *
    (Real.sqrt (Real.sqrt (ν / 2)))⁻¹
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
    simpa using (hzero.comp_sub_left t).symm
  apply (hpow.const_mul C).congr
  intro s hs
  by_cases hst : s = t
  · subst s
    simp [C]
  rw [uIoc_of_le hbt] at hs
  have hst' : 0 < t - s := by
    exact sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  exact (threeHalf_heatGainKernel_eq hν hst').symm

/-- The complete inhomogeneous constant for a `3/2`-order heat gain. -/
def inhomogeneousThreeHalfHeatGain (a : ℝ) : ℝ :=
  1 + (Real.sqrt a)⁻¹ + (Real.sqrt (Real.sqrt a))⁻¹ +
    (Real.sqrt (a / 2))⁻¹ *
      (Real.sqrt (Real.sqrt (a / 2)))⁻¹

theorem inhomogeneousThreeHalfHeatGain_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ inhomogeneousThreeHalfHeatGain a := by
  unfold inhomogeneousThreeHalfHeatGain
  positivity

theorem inv_sqrt_mul_eq_inv_sqrt_mul_rpow_neg_half
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    (Real.sqrt (ν * r))⁻¹ =
      (Real.sqrt ν)⁻¹ * r ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_mul hν.le, mul_inv_rev, Real.sqrt_eq_rpow,
    ← Real.rpow_neg_one, ← Real.rpow_mul hr.le]
  ring

theorem inv_fourthRoot_mul_eq_inv_fourthRoot_mul_rpow_neg_quarter
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    (Real.sqrt (Real.sqrt (ν * r)))⁻¹ =
      (Real.sqrt (Real.sqrt ν))⁻¹ * r ^ (-(1 / 4 : ℝ)) := by
  rw [Real.sqrt_mul hν.le,
    Real.sqrt_mul (Real.sqrt_nonneg ν), mul_inv_rev]
  have hrpow : (Real.sqrt (Real.sqrt r))⁻¹ =
      r ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hr.le, ← Real.rpow_neg_one,
      ← Real.rpow_mul hr.le]
    norm_num
  rw [hrpow, mul_comm]

/-- The complete inhomogeneous `3/2` heat-gain constant is integrable in
the Duhamel time variable. -/
theorem intervalIntegrable_inhomogeneousThreeHalfHeatGain
    (ν : ℝ) (hν : 0 < ν) {b t : ℝ} (hbt : b ≤ t) :
    IntervalIntegrable
      (fun x : ℝ => inhomogeneousThreeHalfHeatGain (ν * (t - x)))
      volume b t := by
  have hhalfPow : IntervalIntegrable
      (fun x : ℝ => (t - x) ^ (-(1 / 2 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
    simpa using (hzero.comp_sub_left t).symm
  have hquarterPow : IntervalIntegrable
      (fun x : ℝ => (t - x) ^ (-(1 / 4 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(1 / 4 : ℝ))
    simpa using (hzero.comp_sub_left t).symm
  have hhalf : IntervalIntegrable
      (fun x : ℝ => (Real.sqrt (ν * (t - x)))⁻¹) volume b t := by
    apply (hhalfPow.const_mul (Real.sqrt ν)⁻¹).congr
    intro x hx
    by_cases hxt : x = t
    · subst x
      simp
    rw [uIoc_of_le hbt] at hx
    exact (inv_sqrt_mul_eq_inv_sqrt_mul_rpow_neg_half
      hν (sub_pos.mpr (lt_of_le_of_ne hx.2 hxt))).symm
  have hquarter : IntervalIntegrable
      (fun x : ℝ => (Real.sqrt (Real.sqrt (ν * (t - x))))⁻¹)
      volume b t := by
    apply (hquarterPow.const_mul (Real.sqrt (Real.sqrt ν))⁻¹).congr
    intro x hx
    by_cases hxt : x = t
    · subst x
      simp
    rw [uIoc_of_le hbt] at hx
    exact (inv_fourthRoot_mul_eq_inv_fourthRoot_mul_rpow_neg_quarter
      hν (sub_pos.mpr (lt_of_le_of_ne hx.2 hxt))).symm
  have hthree : IntervalIntegrable
      (fun x : ℝ =>
        (Real.sqrt ((ν * (t - x)) / 2))⁻¹ *
          (Real.sqrt (Real.sqrt ((ν * (t - x)) / 2)))⁻¹)
      volume b t :=
    intervalIntegrable_threeHalf_heatGainKernel ν hν hbt
  simpa only [inhomogeneousThreeHalfHeatGain] using
    ((intervalIntegrable_const (c := (1 : ℝ))).add hhalf).add hquarter |>.add hthree

/-- Translation of the endpoint singularity gives one common tail budget on
all shorter subintervals. -/
theorem integral_inhomogeneousThreeHalfHeatGain_tail_le
    (ν : ℝ) (hν : 0 < ν) {M b t T : ℝ}
    (hbt : b ≤ t) (htT : t ≤ T) :
    (∫ x in Ioc b t,
      inhomogeneousThreeHalfHeatGain (ν * (t - x)) * M ^ 2) ≤
      ∫ r in Ioc 0 (T - b),
        inhomogeneousThreeHalfHeatGain (ν * r) * M ^ 2 := by
  let F : ℝ → ℝ := fun r =>
    inhomogeneousThreeHalfHeatGain (ν * r) * M ^ 2
  have hbT : b ≤ T := hbt.trans htT
  have hL : 0 ≤ T - b := sub_nonneg.mpr hbT
  have hreflect := intervalIntegrable_inhomogeneousThreeHalfHeatGain
    ν hν (b := 0) (t := T - b) hL
  have hFbase : IntervalIntegrable
      (fun r : ℝ => inhomogeneousThreeHalfHeatGain (ν * r))
      volume 0 (T - b) := by
    have hcomp := (hreflect.comp_sub_left (T - b)).symm
    simpa only [sub_zero, sub_self, sub_sub_cancel] using hcomp
  have hF : IntervalIntegrable F volume 0 (T - b) := by
    simpa only [F, mul_comm] using hFbase.const_mul (M ^ 2)
  have hFnonneg : ∀ᵐ r ∂volume.restrict (Ioc 0 (T - b)), 0 ≤ F r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg
      (inhomogeneousThreeHalfHeatGain_nonneg
        (mul_nonneg hν.le hr.1.le)) (sq_nonneg M)
  rw [← intervalIntegral.integral_of_le hbt,
    ← intervalIntegral.integral_of_le hL]
  change (∫ x in b..t, F (t - x)) ≤ ∫ r in 0..T - b, F r
  rw [intervalIntegral.integral_comp_sub_left F t, sub_self]
  exact intervalIntegral.integral_mono_interval le_rfl (sub_nonneg.mpr hbt)
    (sub_le_sub_right htT b) hFnonneg hF

/-- Coefficientwise, positive heat time raises an arbitrary real polynomial
moment by `3/2`.  The statement uses the literal decoded coefficient of the
completed heat carrier. -/
theorem polynomialMomentAmplitude_weightedHeatFlow_add_threeHalves_le
    (s ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    polynomialMomentAmplitude (s + 3 / 2)
        (weightedHeatFlow ν r hν.le hr.le u) k ≤
      inhomogeneousThreeHalfHeatGain (ν * r) *
        polynomialMomentAmplitude s u k := by
  have hνr : 0 < ν * r := mul_pos hν hr
  let q : ℝ := ‖complexFrequency (latticeFrequency k)‖
  have hq : 0 ≤ q := norm_nonneg _
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hheat := complexEuclideanNorm_heatLeray_le_decay ν r k
    (weightedLatticeCoefficient u k)
  have hdecay : complexHeatDecay ν r (latticeFrequency k) =
      Real.exp (-((ν * r) * q * q)) := by
    unfold q complexHeatDecay FrequencyHeatLeray.heatDecay
    rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
    congr 1
    ring
  have hgain : latticeModeWeight k ^ (3 / 2 : ℝ) *
      complexHeatDecay ν r (latticeFrequency k) ≤
        inhomogeneousThreeHalfHeatGain (ν * r) := by
    rw [hdecay]
    unfold latticeModeWeight inhomogeneousThreeHalfHeatGain q
    exact one_add_rpow_threeHalves_mul_exp_neg_mul_sq_le hνr hq
  unfold polynomialMomentAmplitude
  rw [weightedLatticeCoefficient_weightedHeatFlow]
  calc
    latticeModeWeight k ^ (s + 3 / 2) *
        complexEuclideanNorm
          (complexFrequencyHeatLeray ν r (latticeFrequency k)
            (weightedLatticeCoefficient u k)) ≤
      latticeModeWeight k ^ (s + 3 / 2) *
        (complexHeatDecay ν r (latticeFrequency k) *
          complexEuclideanNorm (weightedLatticeCoefficient u k)) :=
      mul_le_mul_of_nonneg_left hheat
        (Real.rpow_nonneg hw.le (s + 3 / 2))
    _ = (latticeModeWeight k ^ (3 / 2 : ℝ) *
          complexHeatDecay ν r (latticeFrequency k)) *
        (latticeModeWeight k ^ s *
          complexEuclideanNorm (weightedLatticeCoefficient u k)) := by
      rw [Real.rpow_add hw]
      ring
    _ ≤ inhomogeneousThreeHalfHeatGain (ν * r) *
        (latticeModeWeight k ^ s *
          complexEuclideanNorm (weightedLatticeCoefficient u k)) :=
      mul_le_mul_of_nonneg_right hgain
        (mul_nonneg (Real.rpow_nonneg hw.le s) (norm_nonneg _))

/-- Positive heat time maps a finite `S_s` moment into `S_(s+3/2)`. -/
theorem latticePolynomialMoment_weightedHeatFlow_add_threeHalves
    (s ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticePolynomialMoment s u) :
    LatticePolynomialMoment (s + 3 / 2)
      (weightedHeatFlow ν r hν.le hr.le u) := by
  exact (hu.mul_left (inhomogeneousThreeHalfHeatGain (ν * r))).of_nonneg_of_le
    (polynomialMomentAmplitude_nonneg _ _)
    (polynomialMomentAmplitude_weightedHeatFlow_add_threeHalves_le
      s ν r hν hr u)

/-- Quantitative `S_s → S_(s+3/2)` heat estimate. -/
theorem polynomialMoment_weightedHeatFlow_add_threeHalves_le
    (s ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticePolynomialMoment s u) :
    polynomialMoment (s + 3 / 2)
        (weightedHeatFlow ν r hν.le hr.le u) ≤
      inhomogeneousThreeHalfHeatGain (ν * r) * polynomialMoment s u := by
  unfold polynomialMoment
  have hout := latticePolynomialMoment_weightedHeatFlow_add_threeHalves
    s ν r hν hr u hu
  have hright := hu.mul_left (inhomogeneousThreeHalfHeatGain (ν * r))
  calc
    (∑' k, polynomialMomentAmplitude (s + 3 / 2)
      (weightedHeatFlow ν r hν.le hr.le u) k) ≤
        ∑' k, inhomogeneousThreeHalfHeatGain (ν * r) *
          polynomialMomentAmplitude s u k :=
      hout.tsum_le_tsum
        (polynomialMomentAmplitude_weightedHeatFlow_add_threeHalves_le
          s ν r hν hr u) hright
    _ = inhomogeneousThreeHalfHeatGain (ν * r) *
        ∑' k, polynomialMomentAmplitude s u k := tsum_mul_left

theorem polynomialMomentAmplitude_weightedHeatFlow_le
    (p ν r : ℝ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    polynomialMomentAmplitude p (weightedHeatFlow ν r hν hr u) k ≤
      polynomialMomentAmplitude p u k := by
  unfold polynomialMomentAmplitude
  rw [weightedLatticeCoefficient_weightedHeatFlow]
  exact mul_le_mul_of_nonneg_left
    (complexEuclideanNorm_heatLeray_le ν r hν hr k
      (weightedLatticeCoefficient u k))
    (Real.rpow_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) p)

theorem latticePolynomialMoment_weightedHeatFlow
    (p ν r : ℝ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (u : WeightedLatticeBanach) (hu : LatticePolynomialMoment p u) :
    LatticePolynomialMoment p (weightedHeatFlow ν r hν hr u) :=
  hu.of_nonneg_of_le (polynomialMomentAmplitude_nonneg p _)
    (polynomialMomentAmplitude_weightedHeatFlow_le p ν r hν hr u)

theorem polynomialMoment_weightedHeatFlow_le
    (p ν r : ℝ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (u : WeightedLatticeBanach) (hu : LatticePolynomialMoment p u) :
    polynomialMoment p (weightedHeatFlow ν r hν hr u) ≤ polynomialMoment p u := by
  unfold polynomialMoment
  exact (latticePolynomialMoment_weightedHeatFlow p ν r hν hr u hu).tsum_le_tsum
    (polynomialMomentAmplitude_weightedHeatFlow_le p ν r hν hr u) hu

/-- The decoded order-`p` density is the order-`p-1` multiplier applied to
the completed carrier coordinate. -/
theorem polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm
    (p : ℝ) (u : WeightedLatticeBanach) (k : LatticeMode) :
    polynomialMomentAmplitude p u k =
      latticeModeWeight k ^ (p - 1) * ‖u k‖ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  rw [← latticeWeightedAmplitude_coefficient u k]
  unfold polynomialMomentAmplitude latticeWeightedAmplitude
  rw [show p = (p - 1) + 1 by ring, Real.rpow_add hw, Real.rpow_one]
  ring

/-- Finite polynomial-moment sums pass through the actual Bochner integral.
This is the Tonelli/Fatou interface used for the restarted Duhamel tail. -/
theorem sum_polynomialMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (p : ℝ) (F : Finset LatticeMode)
    (f : α → WeightedLatticeBanach) (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ x ∂μ.restrict S, LatticePolynomialMoment p (f x))
    (hfM : IntegrableOn (fun x => polynomialMoment p (f x)) S μ) :
    (∑ k ∈ F, polynomialMomentAmplitude p (∫ x in S, f x ∂μ) k) ≤
      ∫ x in S, polynomialMoment p (f x) ∂μ := by
  have hcoord (k : LatticeMode) :
      (∫ x in S, f x ∂μ) k = ∫ x in S, f x k ∂μ := by
    change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
        (∫ x in S, f x ∂μ) = _
    exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm hf |>.symm
  have hcoordInt (k : LatticeMode) : IntegrableOn (fun x => f x k) S μ :=
    (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integrable_comp hf
  have htermInt (k : LatticeMode) : IntegrableOn
      (fun x => polynomialMomentAmplitude p (f x) k) S μ := by
    simp_rw [polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm]
    exact (hcoordInt k).norm.const_mul _
  calc
    (∑ k ∈ F, polynomialMomentAmplitude p (∫ x in S, f x ∂μ) k) ≤
        ∑ k ∈ F, latticeModeWeight k ^ (p - 1) *
          (∫ x in S, ‖f x k‖ ∂μ) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm, hcoord k]
      exact mul_le_mul_of_nonneg_left
        (norm_integral_le_integral_norm _)
        (Real.rpow_nonneg
          (zero_le_one.trans (one_le_latticeModeWeight k)) (p - 1))
    _ = ∫ x in S, ∑ k ∈ F, polynomialMomentAmplitude p (f x) k ∂μ := by
      rw [integral_finsetSum F (fun k _ => htermInt k)]
      simp_rw [polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm,
        integral_const_mul]
    _ ≤ ∫ x in S, polynomialMoment p (f x) ∂μ := by
      apply integral_mono_ae
      · exact integrable_finsetSum F fun k _ => htermInt k
      · exact hfM
      · filter_upwards [hfsum] with x hx
        unfold polynomialMoment
        exact hx.sum_le_tsum F fun k _ =>
          polynomialMomentAmplitude_nonneg p (f x) k

/-- The exact order-`p` moment domain is closed under an integrable Bochner
history when the moment masses themselves are integrable. -/
theorem latticePolynomialMoment_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (p : ℝ) (f : α → WeightedLatticeBanach) (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ x ∂μ.restrict S, LatticePolynomialMoment p (f x))
    (hfM : IntegrableOn (fun x => polynomialMoment p (f x)) S μ) :
    LatticePolynomialMoment p (∫ x in S, f x ∂μ) := by
  apply summable_of_sum_le
  · exact polynomialMomentAmplitude_nonneg p _
  · intro F
    exact sum_polynomialMoment_integral_le_integral p F f hf hfsum hfM

/-- Quantitative polynomial-moment bound for an actual Bochner history. -/
theorem polynomialMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (p : ℝ) (f : α → WeightedLatticeBanach) (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ x ∂μ.restrict S, LatticePolynomialMoment p (f x))
    (hfM : IntegrableOn (fun x => polynomialMoment p (f x)) S μ) :
    polynomialMoment p (∫ x in S, f x ∂μ) ≤
      ∫ x in S, polynomialMoment p (f x) ∂μ := by
  unfold polynomialMoment
  apply Real.tsum_le_of_sum_le
  · exact polynomialMomentAmplitude_nonneg p _
  · intro F
    exact sum_polynomialMoment_integral_le_integral p F f hf hfsum hfM

/-- One mode of the actual mild integrand gains `3/2` weights over the
projected forcing at the integration time. -/
theorem polynomialMomentAmplitude_criticalMildPathIntegrand_le
    (p ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {t x : ℝ} (hxt : x < t) (k : LatticeMode) :
    polynomialMomentAmplitude (p + 1 / 2)
        (criticalMildPathIntegrand ν hν u hu t x) k ≤
      inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        (latticeModeWeight k ^ (p - 1) *
          complexEuclideanNorm (projectedModeForcing u k x)) := by
  have hlag : 0 < t - x := sub_pos.mpr hxt
  have hνlag : 0 < ν * (t - x) := mul_pos hν hlag
  let q : ℝ := ‖complexFrequency (latticeFrequency k)‖
  have hq : 0 ≤ q := norm_nonneg _
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hdecay : complexHeatDecay ν (t - x) (latticeFrequency k) =
      Real.exp (-((ν * (t - x)) * q * q)) := by
    unfold q complexHeatDecay FrequencyHeatLeray.heatDecay
    rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
    congr 1
    ring
  have hgain : latticeModeWeight k ^ (3 / 2 : ℝ) *
      complexHeatDecay ν (t - x) (latticeFrequency k) ≤
        inhomogeneousThreeHalfHeatGain (ν * (t - x)) := by
    rw [hdecay]
    unfold latticeModeWeight inhomogeneousThreeHalfHeatGain q
    exact one_add_rpow_threeHalves_mul_exp_neg_mul_sq_le hνlag hq
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
      ν hν (u x) (u x) (hu x) hlag,
    polynomialMomentAmplitude,
    weightedLatticeCoefficient_heatRegularizedSpectralOutput,
    complexFrequencyHeatLeray_apply, complexEuclideanNorm,
    complexEuclideanPoint_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (complexHeatDecay_nonneg ν (t - x) (latticeFrequency k))]
  change latticeModeWeight k ^ (p + 1 / 2) *
      (complexHeatDecay ν (t - x) (latticeFrequency k) *
        complexEuclideanNorm
          (complexLeray (latticeFrequency k)
            (spectralOutputCoefficient k (u x) (u x)))) ≤ _
  change latticeModeWeight k ^ (p + 1 / 2) *
      (complexHeatDecay ν (t - x) (latticeFrequency k) *
        complexEuclideanNorm (projectedModeForcing u k x)) ≤ _
  calc
    latticeModeWeight k ^ (p + 1 / 2) *
        (complexHeatDecay ν (t - x) (latticeFrequency k) *
          complexEuclideanNorm (projectedModeForcing u k x)) =
      (latticeModeWeight k ^ (3 / 2 : ℝ) *
          complexHeatDecay ν (t - x) (latticeFrequency k)) *
        (latticeModeWeight k ^ (p - 1) *
          complexEuclideanNorm (projectedModeForcing u k x)) := by
      rw [show p + 1 / 2 = 3 / 2 + (p - 1) by ring,
        Real.rpow_add hw]
      ring
    _ ≤ inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        (latticeModeWeight k ^ (p - 1) *
          complexEuclideanNorm (projectedModeForcing u k x)) :=
      mul_le_mul_of_nonneg_right hgain
        (mul_nonneg (Real.rpow_nonneg hw.le (p - 1)) (norm_nonneg _))

/-- The literal nonlinear mild integrand maps an `S_p` trajectory slice to
`S_(p+1/2)`, with the exact projected-convolution square on the right. -/
theorem latticePolynomialMoment_criticalMildPathIntegrand_add_half
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {t x : ℝ} (hxt : x < t)
    (hux : LatticePolynomialMoment p (u x)) :
    LatticePolynomialMoment (p + 1 / 2)
      (criticalMildPathIntegrand ν hν u hu t x) := by
  have hforce : Summable fun k => latticeModeWeight k ^ (p - 1) *
      complexEuclideanNorm (projectedModeForcing u k x) := by
    simpa [projectedSpectralConvolutionCoefficient, projectedModeForcing] using
      summable_projectedConvolutionPolynomialMoment p hp (u x) (u x) hux hux
  exact (hforce.mul_left
    (inhomogeneousThreeHalfHeatGain (ν * (t - x)))).of_nonneg_of_le
      (polynomialMomentAmplitude_nonneg _ _)
      (polynomialMomentAmplitude_criticalMildPathIntegrand_le
        p ν hν u hu hxt)

/-- Quantitative moment estimate for the actual evolving Duhamel integrand. -/
theorem polynomialMoment_criticalMildPathIntegrand_add_half_le
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {t x : ℝ} (hxt : x < t)
    (hux : LatticePolynomialMoment p (u x)) :
    polynomialMoment (p + 1 / 2)
        (criticalMildPathIntegrand ν hν u hu t x) ≤
      inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        polynomialMoment p (u x) ^ 2 := by
  have hνlag : 0 < ν * (t - x) := mul_pos hν (sub_pos.mpr hxt)
  unfold polynomialMoment
  have hout := latticePolynomialMoment_criticalMildPathIntegrand_add_half
    p ν hp hν u hu hxt hux
  have hforce := summable_projectedConvolutionPolynomialMoment
    p hp (u x) (u x) hux hux
  have hright : Summable fun k =>
      inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        (latticeModeWeight k ^ (p - 1) *
          complexEuclideanNorm (projectedModeForcing u k x)) := by
    apply Summable.mul_left
    simpa [projectedSpectralConvolutionCoefficient, projectedModeForcing] using hforce
  calc
    (∑' k, polynomialMomentAmplitude (p + 1 / 2)
      (criticalMildPathIntegrand ν hν u hu t x) k) ≤
        ∑' k, inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
          (latticeModeWeight k ^ (p - 1) *
            complexEuclideanNorm (projectedModeForcing u k x)) :=
      hout.tsum_le_tsum
        (polynomialMomentAmplitude_criticalMildPathIntegrand_le
          p ν hν u hu hxt) hright
    _ = inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        (∑' k, latticeModeWeight k ^ (p - 1) *
          complexEuclideanNorm (projectedModeForcing u k x)) := tsum_mul_left
    _ ≤ inhomogeneousThreeHalfHeatGain (ν * (t - x)) *
        polynomialMoment p (u x) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (tsum_projectedModeForcing_polynomial_sub_one_le p hp u x hux)
        (inhomogeneousThreeHalfHeatGain_nonneg hνlag.le)

theorem polynomialMoment_nonneg (p : ℝ) (u : WeightedLatticeBanach) :
    0 ≤ polynomialMoment p u := by
  unfold polynomialMoment
  exact tsum_nonneg (polynomialMomentAmplitude_nonneg p u)

theorem polynomialMomentAmplitude_mono
    {p q : ℝ} (hpq : p ≤ q) (u : WeightedLatticeBanach) (k : LatticeMode) :
    polynomialMomentAmplitude p u k ≤ polynomialMomentAmplitude q u k := by
  unfold polynomialMomentAmplitude
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_latticeModeWeight k) hpq)
    (norm_nonneg _)

theorem latticePolynomialMoment_mono
    {p q : ℝ} (hpq : p ≤ q) (u : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment q u) : LatticePolynomialMoment p u :=
  hu.of_nonneg_of_le (polynomialMomentAmplitude_nonneg p u)
    (polynomialMomentAmplitude_mono hpq u)

theorem polynomialMoment_mono
    {p q : ℝ} (hpq : p ≤ q) (u : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment q u) :
    polynomialMoment p u ≤ polynomialMoment q u := by
  unfold polynomialMoment
  exact (latticePolynomialMoment_mono hpq u hu).tsum_le_tsum
    (polynomialMomentAmplitude_mono hpq u) hu

theorem polynomialMomentAmplitude_add_le
    (p : ℝ) (u v : WeightedLatticeBanach) (k : LatticeMode) :
    polynomialMomentAmplitude p (u + v) k ≤
      polynomialMomentAmplitude p u k + polynomialMomentAmplitude p v k := by
  simp_rw [polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm]
  change latticeModeWeight k ^ (p - 1) * ‖u k + v k‖ ≤ _
  calc
    latticeModeWeight k ^ (p - 1) * ‖u k + v k‖ ≤
        latticeModeWeight k ^ (p - 1) * (‖u k‖ + ‖v k‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _)
        (Real.rpow_nonneg
          (zero_le_one.trans (one_le_latticeModeWeight k)) (p - 1))
    _ = latticeModeWeight k ^ (p - 1) * ‖u k‖ +
        latticeModeWeight k ^ (p - 1) * ‖v k‖ := by ring

theorem latticePolynomialMoment_add
    (p : ℝ) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment p u) (hv : LatticePolynomialMoment p v) :
    LatticePolynomialMoment p (u + v) :=
  (hu.add hv).of_nonneg_of_le (polynomialMomentAmplitude_nonneg p (u + v))
    (polynomialMomentAmplitude_add_le p u v)

theorem polynomialMoment_add_le
    (p : ℝ) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment p u) (hv : LatticePolynomialMoment p v) :
    polynomialMoment p (u + v) ≤ polynomialMoment p u + polynomialMoment p v := by
  unfold polynomialMoment
  calc
    (∑' k, polynomialMomentAmplitude p (u + v) k) ≤
        ∑' k, (polynomialMomentAmplitude p u k +
          polynomialMomentAmplitude p v k) :=
      (latticePolynomialMoment_add p u v hu hv).tsum_le_tsum
        (polynomialMomentAmplitude_add_le p u v) (hu.add hv)
    _ = (∑' k, polynomialMomentAmplitude p u k) +
        ∑' k, polynomialMomentAmplitude p v k := hu.tsum_add hv

/-- Polynomial moment mass of the actual mild integrand is measurable in the
integration variable. -/
theorem measurable_polynomialMoment_criticalMildPathIntegrand
    (p ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x)) (t : ℝ) :
    Measurable fun x =>
      polynomialMoment p (criticalMildPathIntegrand ν hν u hu t x) := by
  unfold polynomialMoment
  simp_rw [polynomialMomentAmplitude_eq_rpow_sub_one_mul_norm]
  exact Measurable.tsum fun k => measurable_const.mul
    ((stronglyMeasurable_criticalMildPathIntegrand_apply
      ν hν u huc hu t k).norm.measurable)

/-- **Restart-tail induction step.** Uniform `S_p` control on `(b,t]`
produces an actual `S_(p+1/2)` Bochner tail.  The singular factor is the
proved integrable inhomogeneous `3/2` heat kernel, and the nonlinear mass is
the square supplied by the exact countable convolution theorem. -/
theorem criticalMildDuhamelTail_polynomialMoment_add_half
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R M b t : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hbt : b ≤ t)
    (huR : ∀ x ∈ Ioc (0 : ℝ) t, ‖u x‖ ≤ R)
    (huM : ∀ x ∈ Ioc b t,
      LatticePolynomialMoment p (u x) ∧ polynomialMoment p (u x) ≤ M) :
    LatticePolynomialMoment (p + 1 / 2)
        (criticalMildDuhamelTail ν hν u hu b t) ∧
      polynomialMoment (p + 1 / 2)
          (criticalMildDuhamelTail ν hν u hu b t) ≤
        ∫ x in Ioc b t,
          inhomogeneousThreeHalfHeatGain (ν * (t - x)) * M ^ 2 := by
  let f : ℝ → WeightedLatticeBanach :=
    fun x => criticalMildPathIntegrand ν hν u hu t x
  let g : ℝ → ℝ := fun x =>
    inhomogeneousThreeHalfHeatGain (ν * (t - x)) * M ^ 2
  have hf : IntegrableOn f (Ioc b t) volume := by
    exact integrableOn_criticalMildDuhamelTailIntegrand
      ν hν u huc hu hR hb hbt huR
  have hne : ∀ᵐ x ∂volume.restrict (Ioc b t), x ≠ t :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hfsum : ∀ᵐ x ∂volume.restrict (Ioc b t),
      LatticePolynomialMoment (p + 1 / 2) (f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with x hx hxt
    exact latticePolynomialMoment_criticalMildPathIntegrand_add_half
      p ν hp hν u hu (lt_of_le_of_ne hx.2 hxt) (huM x hx).1
  have hg : IntegrableOn g (Ioc b t) volume := by
    have hK := intervalIntegrable_inhomogeneousThreeHalfHeatGain ν hν hbt
    have hKI : IntegrableOn
        (fun x => inhomogeneousThreeHalfHeatGain (ν * (t - x)))
        (Ioc b t) volume := by
      simpa [uIoc_of_le hbt] using
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hbt).mp hK
    change Integrable g (volume.restrict (Ioc b t))
    simpa only [g, mul_comm] using hKI.const_mul (M ^ 2)
  have hdom : (fun x => ‖polynomialMoment (p + 1 / 2) (f x)‖) ≤ᵐ[
      volume.restrict (Ioc b t)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with x hx hxt
    rw [Real.norm_eq_abs,
      abs_of_nonneg (polynomialMoment_nonneg (p + 1 / 2) (f x))]
    have hraw := polynomialMoment_criticalMildPathIntegrand_add_half_le
      p ν hp hν u hu (lt_of_le_of_ne hx.2 hxt) (huM x hx).1
    have hsq : polynomialMoment p (u x) ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (polynomialMoment_nonneg p (u x)) hM).2 (huM x hx).2
    exact hraw.trans (mul_le_mul_of_nonneg_left hsq
      (inhomogeneousThreeHalfHeatGain_nonneg
        (mul_nonneg hν.le (sub_nonneg.mpr hx.2))))
  have hdom' : (fun x => polynomialMoment (p + 1 / 2) (f x)) ≤ᵐ[
      volume.restrict (Ioc b t)] g := by
    filter_upwards [hdom] with x hx
    exact (le_abs_self _).trans hx
  have hfM : IntegrableOn (fun x => polynomialMoment (p + 1 / 2) (f x))
      (Ioc b t) volume := by
    apply hg.mono'
      (measurable_polynomialMoment_criticalMildPathIntegrand
        (p + 1 / 2) ν hν u huc hu t).aestronglyMeasurable
    exact hdom
  unfold criticalMildDuhamelTail
  change LatticePolynomialMoment (p + 1 / 2) (∫ x in Ioc b t, f x) ∧
    polynomialMoment (p + 1 / 2) (∫ x in Ioc b t, f x) ≤ ∫ x in Ioc b t, g x
  refine ⟨latticePolynomialMoment_integral (p + 1 / 2) f hf hfsum hfM, ?_⟩
  exact (polynomialMoment_integral_le_integral
    (p + 1 / 2) f hf hfsum hfM).trans (integral_mono_ae hfM hg hdom')

/-- **Actual mild-trajectory induction.** Restarting at a positive time `b`
combines a smoothed terminal value with the just-controlled nonlinear tail,
raising a uniform `S_p` interval to `S_(p+1/2)` at its right endpoint. -/
theorem mildTrajectory_polynomialMoment_add_half
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R M b t : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hbt : b < t)
    (huR : ∀ x ∈ Ioc (0 : ℝ) t, ‖u x‖ ≤ R)
    (hmild_b : u b = criticalMildImage ν hν u₀ u hu b hb)
    (hmild_t : u t = criticalMildImage ν hν u₀ u hu t (hb.trans hbt.le))
    (hub : LatticePolynomialMoment p (u b))
    (huM : ∀ x ∈ Ioc b t,
      LatticePolynomialMoment p (u x) ∧ polynomialMoment p (u x) ≤ M) :
    LatticePolynomialMoment (p + 1 / 2) (u t) := by
  have hr : 0 < t - b := sub_pos.mpr hbt
  have hadd : b + (t - b) = t := by ring
  have htail := criticalMildDuhamelTail_polynomialMoment_add_half
    p ν hp hν u huc hu hR hM hb hbt.le huR huM
  have hheatHigh := latticePolynomialMoment_weightedHeatFlow_add_threeHalves
    p ν (t - b) hν hr (u b) hub
  have hheat : LatticePolynomialMoment (p + 1 / 2)
      (weightedHeatFlow ν (t - b) hν.le hr.le (u b)) :=
    latticePolynomialMoment_mono (by norm_num)
      (weightedHeatFlow ν (t - b) hν.le hr.le (u b)) hheatHigh
  have hrestarted :
      criticalMildRestartImage ν hν u hu b (t - b) hr.le = u t := by
    simpa only [hadd] using
      (criticalMildRestartImage_eq_shifted_trajectory
        ν hν u₀ u huc hu hR hb hr.le
          (fun x hx => huR x (by rw [hadd] at hx; exact hx))
          hmild_b (by simpa only [hadd] using hmild_t))
  have hrepr : u t =
      weightedHeatFlow ν (t - b) hν.le hr.le (u b) +
        criticalMildDuhamelTail ν hν u hu b t := by
    rw [← hrestarted]
    unfold criticalMildRestartImage criticalMildTerminalData
    rw [criticalMildDuhamelRestartTail_eq_tail ν hν u hu b (t - b) hr.le]
    rw [hadd]
  rw [hrepr]
  exact latticePolynomialMoment_add (p + 1 / 2) _ _ hheat htail.1

/-- One explicit compact-interval budget for the half-order induction step. -/
def higherMomentStepBudget (ν M a b T : ℝ) : ℝ :=
  inhomogeneousThreeHalfHeatGain (ν * (a - b)) * M +
    ∫ r in Ioc 0 (T - b),
      inhomogeneousThreeHalfHeatGain (ν * r) * M ^ 2

/-- **Uniform half-order bootstrap on nested positive intervals.**  A common
`S_p` bound on `[b,T]` gives a common `S_(p+1/2)` bound on every strictly
interior `[a,T]`.  All terms are derived from the actual restarted mild
identity; the bound depends only on the previous mass, viscosity, and the two
cutoffs. -/
theorem exists_uniform_polynomialMoment_add_half_on_compactPositiveInterval
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R M b a T : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hba : b < a) (haT : a ≤ T)
    (huR : ∀ x ∈ Ioc (0 : ℝ) T, ‖u x‖ ≤ R)
    (hmild : ∀ x (hx : x ∈ Icc (0 : ℝ) T),
      u x = criticalMildImage ν hν u₀ u hu x hx.1)
    (huM : ∀ x ∈ Icc b T,
      LatticePolynomialMoment p (u x) ∧ polynomialMoment p (u x) ≤ M) :
    0 ≤ higherMomentStepBudget ν M a b T ∧
      ∀ t ∈ Icc a T,
        LatticePolynomialMoment (p + 1 / 2) (u t) ∧
          polynomialMoment (p + 1 / 2) (u t) ≤
            higherMomentStepBudget ν M a b T := by
  have hbT : b ≤ T := hba.le.trans haT
  have hgap : 0 < a - b := sub_pos.mpr hba
  have hkernel : 0 ≤ inhomogeneousThreeHalfHeatGain (ν * (a - b)) :=
    inhomogeneousThreeHalfHeatGain_nonneg (mul_nonneg hν.le hgap.le)
  have hintegral : 0 ≤ ∫ r in Ioc 0 (T - b),
      inhomogeneousThreeHalfHeatGain (ν * r) * M ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg
      (inhomogeneousThreeHalfHeatGain_nonneg
        (mul_nonneg hν.le hr.1.le)) (sq_nonneg M)
  have hbudget : 0 ≤ higherMomentStepBudget ν M a b T := by
    unfold higherMomentStepBudget
    exact add_nonneg (mul_nonneg hkernel hM) hintegral
  refine ⟨hbudget, ?_⟩
  intro t ht
  have hbt : b < t := hba.trans_le ht.1
  have ht0 : 0 ≤ t := hb.trans hbt.le
  have huRt : ∀ x ∈ Ioc (0 : ℝ) t, ‖u x‖ ≤ R := by
    intro x hx
    exact huR x ⟨hx.1, hx.2.trans ht.2⟩
  have hmild_b : u b = criticalMildImage ν hν u₀ u hu b hb :=
    hmild b ⟨hb, hbT⟩
  have hmild_t : u t = criticalMildImage ν hν u₀ u hu t ht0 :=
    hmild t ⟨ht0, ht.2⟩
  have huMbt : ∀ x ∈ Ioc b t,
      LatticePolynomialMoment p (u x) ∧ polynomialMoment p (u x) ≤ M := by
    intro x hx
    exact huM x ⟨hx.1.le, hx.2.trans ht.2⟩
  have hub := (huM b ⟨le_rfl, hbT⟩).1
  have hmember := mildTrajectory_polynomialMoment_add_half
    p ν hp hν u₀ u huc hu hR hM hb hbt huRt hmild_b hmild_t hub huMbt
  refine ⟨hmember, ?_⟩
  have hr : 0 < t - b := sub_pos.mpr hbt
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have hadd : b + (t - b) = t := by ring
  have htail := criticalMildDuhamelTail_polynomialMoment_add_half
    p ν hp hν u huc hu hR hM hb hbt.le huRt huMbt
  let v : WeightedLatticeBanach :=
    weightedHeatFlow ν (a - b) hν.le hgap.le (u b)
  have hvHigh : LatticePolynomialMoment (p + 3 / 2) v := by
    dsimp [v]
    exact latticePolynomialMoment_weightedHeatFlow_add_threeHalves
      p ν (a - b) hν hgap (u b) hub
  have hv : LatticePolynomialMoment (p + 1 / 2) v :=
    latticePolynomialMoment_mono (by norm_num) v hvHigh
  have hsemigroup : weightedHeatFlow ν (t - b) hν.le hr.le (u b) =
      weightedHeatFlow ν (t - a) hν.le hta v := by
    dsimp [v]
    rw [← weightedHeatFlow_semigroup]
    congr 2 <;> ring
  have hheatMember : LatticePolynomialMoment (p + 1 / 2)
      (weightedHeatFlow ν (t - b) hν.le hr.le (u b)) := by
    rw [hsemigroup]
    exact latticePolynomialMoment_weightedHeatFlow
      (p + 1 / 2) ν (t - a) hν.le hta v hv
  have hvBound : polynomialMoment (p + 1 / 2) v ≤
      inhomogeneousThreeHalfHeatGain (ν * (a - b)) * M := by
    calc
      polynomialMoment (p + 1 / 2) v ≤ polynomialMoment (p + 3 / 2) v :=
        polynomialMoment_mono (by norm_num) v hvHigh
      _ ≤ inhomogeneousThreeHalfHeatGain (ν * (a - b)) *
          polynomialMoment p (u b) := by
        dsimp [v]
        exact polynomialMoment_weightedHeatFlow_add_threeHalves_le
          p ν (a - b) hν hgap (u b) hub
      _ ≤ inhomogeneousThreeHalfHeatGain (ν * (a - b)) * M :=
        mul_le_mul_of_nonneg_left (huM b ⟨le_rfl, hbT⟩).2 hkernel
  have hheatBound : polynomialMoment (p + 1 / 2)
      (weightedHeatFlow ν (t - b) hν.le hr.le (u b)) ≤
        inhomogeneousThreeHalfHeatGain (ν * (a - b)) * M := by
    rw [hsemigroup]
    exact (polynomialMoment_weightedHeatFlow_le
      (p + 1 / 2) ν (t - a) hν.le hta v hv).trans hvBound
  have htailBound : polynomialMoment (p + 1 / 2)
      (criticalMildDuhamelTail ν hν u hu b t) ≤
        ∫ r in Ioc 0 (T - b),
          inhomogeneousThreeHalfHeatGain (ν * r) * M ^ 2 :=
    htail.2.trans
      (integral_inhomogeneousThreeHalfHeatGain_tail_le
        ν hν hbt.le ht.2)
  have hrestarted :
      criticalMildRestartImage ν hν u hu b (t - b) hr.le = u t := by
    simpa only [hadd] using
      (criticalMildRestartImage_eq_shifted_trajectory
        ν hν u₀ u huc hu hR hb hr.le
          (fun x hx => huRt x (by rw [hadd] at hx; exact hx))
          hmild_b (by simpa only [hadd] using hmild_t))
  have hrepr : u t =
      weightedHeatFlow ν (t - b) hν.le hr.le (u b) +
        criticalMildDuhamelTail ν hν u hu b t := by
    rw [← hrestarted]
    unfold criticalMildRestartImage criticalMildTerminalData
    rw [criticalMildDuhamelRestartTail_eq_tail ν hν u hu b (t - b) hr.le,
      hadd]
  rw [hrepr]
  exact (polynomialMoment_add_le (p + 1 / 2) _ _ hheatMember htail.1).trans
    (add_le_add hheatBound htailBound)

/-- Orders visited by the spatial smoothing bootstrap. -/
def iteratedHalfOrder (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => iteratedHalfOrder p n + 1 / 2

theorem one_le_iteratedHalfOrder {p : ℝ} (hp : 1 ≤ p) :
    ∀ n, 1 ≤ iteratedHalfOrder p n
  | 0 => hp
  | n + 1 => (one_le_iteratedHalfOrder hp n).trans
      (le_add_of_nonneg_right (by norm_num))

/-- Recursive quantitative budget attached to a strictly nested family of
positive cutoffs. -/
def iteratedHigherMomentBudget
    (ν T : ℝ) (cut : ℕ → ℝ) (M : ℝ) : ℕ → ℝ
  | 0 => M
  | n + 1 => higherMomentStepBudget ν
      (iteratedHigherMomentBudget ν T cut M n) (cut (n + 1)) (cut n) T

/-- **All finite spatial moments, uniformly on nested positive-time
intervals.** Each induction step is the preceding actual restarted mild
trajectory theorem.  Thus the statement constructs every finite rung from
one genuine initial moment bound, rather than assuming an all-moment bundle. -/
theorem uniform_iteratedHalfOrder_on_nestedPositiveIntervals
    (p ν : ℝ) (hp : 1 ≤ p) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R M T : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (cut : ℕ → ℝ) (hcut0 : ∀ n, 0 ≤ cut n)
    (hcut : ∀ n, cut n < cut (n + 1))
    (hcutT : ∀ n, cut n ≤ T)
    (huR : ∀ x ∈ Ioc (0 : ℝ) T, ‖u x‖ ≤ R)
    (hmild : ∀ x (hx : x ∈ Icc (0 : ℝ) T),
      u x = criticalMildImage ν hν u₀ u hu x hx.1)
    (hbase : ∀ t ∈ Icc (cut 0) T,
      LatticePolynomialMoment p (u t) ∧ polynomialMoment p (u t) ≤ M) :
    ∀ n,
      0 ≤ iteratedHigherMomentBudget ν T cut M n ∧
      ∀ t ∈ Icc (cut n) T,
        LatticePolynomialMoment (iteratedHalfOrder p n) (u t) ∧
          polynomialMoment (iteratedHalfOrder p n) (u t) ≤
            iteratedHigherMomentBudget ν T cut M n := by
  intro n
  induction n with
  | zero =>
      exact ⟨hM, hbase⟩
  | succ n ih =>
      simpa only [iteratedHalfOrder, iteratedHigherMomentBudget] using
        (exists_uniform_polynomialMoment_add_half_on_compactPositiveInterval
          (iteratedHalfOrder p n) ν (one_le_iteratedHalfOrder hp n) hν
          u₀ u huc hu hR ih.1 (hcut0 n) (hcut n) (hcutT (n + 1))
          huR hmild ih.2)

theorem latticePolynomialMoment_two_of_twoWeight
    (u : WeightedLatticeBanach)
    (hu : LatticeTwoWeightL1 (weightedLatticeCoefficient u)) :
    LatticePolynomialMoment 2 u := by
  change Summable fun k => latticeModeWeight k ^ (2 : ℝ) *
    complexEuclideanNorm (weightedLatticeCoefficient u k)
  unfold LatticeTwoWeightL1 at hu
  simpa only [Real.rpow_two] using hu

theorem polynomialMoment_two_eq
    (u : WeightedLatticeBanach) :
    polynomialMoment 2 u =
      ∑' k, latticeModeWeight k ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k) := by
  unfold polynomialMoment polynomialMomentAmplitude
  simp only [Real.rpow_two]

/-- Canonical increasing cutoffs from `a/2` toward `a`. -/
def canonicalSmoothCutoff (a : ℝ) (n : ℕ) : ℝ :=
  a * (1 - 1 / ((n : ℝ) + 2))

theorem canonicalSmoothCutoff_zero (a : ℝ) :
    canonicalSmoothCutoff a 0 = a / 2 := by
  unfold canonicalSmoothCutoff
  norm_num
  ring

theorem canonicalSmoothCutoff_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ canonicalSmoothCutoff a n := by
  unfold canonicalSmoothCutoff
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hinv : 1 / ((n : ℝ) + 2) ≤ (1 : ℝ) := by
    simpa only [div_eq_mul_inv, one_mul, inv_one] using
      one_div_le_one_div_of_le zero_lt_one hd
  exact mul_nonneg ha (sub_nonneg.mpr hinv)

theorem canonicalSmoothCutoff_strictMono {a : ℝ} (ha : 0 < a) (n : ℕ) :
    canonicalSmoothCutoff a n < canonicalSmoothCutoff a (n + 1) := by
  unfold canonicalSmoothCutoff
  apply mul_lt_mul_of_pos_left _ ha
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hstep : (n : ℝ) + 2 < ((n + 1 : ℕ) : ℝ) + 2 := by
    push_cast
    norm_num
  have hinv := one_div_lt_one_div_of_lt hd hstep
  linarith

theorem canonicalSmoothCutoff_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    canonicalSmoothCutoff a n ≤ a := by
  unfold canonicalSmoothCutoff
  have hinv : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
  nlinarith

/-- **Actual all-order spatial smoothing on every compact positive-time
interval.** Starting only from the native bounded critical mild trajectory,
the earlier uniform two-weight theorem supplies the base rung; the restarted
convolution/heat induction above then constructs a common bound for every
finite half-order on `[a,T]`. -/
theorem exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R a T : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a ≤ T)
    (huR : ∀ x ∈ Ioc (0 : ℝ) T, ‖u x‖ ≤ R)
    (hmild : ∀ x (hx : x ∈ Icc (0 : ℝ) T),
      u x = criticalMildImage ν hν u₀ u hu x hx.1) :
    ∃ B : ℕ → ℝ,
      (∀ n, 0 ≤ B n) ∧
      ∀ n t, t ∈ Icc a T →
        LatticePolynomialMoment (iteratedHalfOrder 2 n) (u t) ∧
          polynomialMoment (iteratedHalfOrder 2 n) (u t) ≤ B n := by
  have ha2 : 0 < a / 2 := by positivity
  have ha2T : a / 2 ≤ T := by linarith
  obtain ⟨b₀, hb₀, hb₀a, hunit, hinterior, hbaseBudget,
      hbaseUniform⟩ :=
    exists_uniform_halfGenerator_on_compactPositiveInterval
      ν hν u₀ hu₀ u huc hu hR ha2 ha2T huR hmild
  let M : ℝ := R + compactHalfGeneratorBudget ν u₀ R (a / 2) b₀ T
  let cut : ℕ → ℝ := canonicalSmoothCutoff a
  have hM : 0 ≤ M := add_nonneg hR hbaseBudget
  have hbase : ∀ t ∈ Icc (cut 0) T,
      LatticePolynomialMoment 2 (u t) ∧ polynomialMoment 2 (u t) ≤ M := by
    intro t ht
    have ht' : t ∈ Icc (a / 2) T := by
      simpa only [cut, canonicalSmoothCutoff_zero] using ht
    have h := hbaseUniform t ht'
    refine ⟨latticePolynomialMoment_two_of_twoWeight (u t) h.2.1, ?_⟩
    rw [polynomialMoment_two_eq]
    exact h.2.2.1
  have hcut0 : ∀ n, 0 ≤ cut n :=
    fun n => canonicalSmoothCutoff_nonneg ha.le n
  have hcut : ∀ n, cut n < cut (n + 1) :=
    fun n => canonicalSmoothCutoff_strictMono ha n
  have hcutT : ∀ n, cut n ≤ T := fun n =>
    (canonicalSmoothCutoff_le ha.le n).trans haT
  have hall := uniform_iteratedHalfOrder_on_nestedPositiveIntervals
    2 ν (by norm_num) hν u₀ u huc hu hR hM cut hcut0 hcut hcutT
      huR hmild hbase
  let B : ℕ → ℝ := iteratedHigherMomentBudget ν T cut M
  refine ⟨B, fun n => (hall n).1, ?_⟩
  intro n t ht
  exact (hall n).2 t ⟨(canonicalSmoothCutoff_le ha.le n).trans ht.1, ht.2⟩

end Navier.Analysis.CriticalMildHigherUniformMoments

#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.polynomialMoment_weightedHeatFlow_add_threeHalves_le
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.polynomialMoment_integral_le_integral
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.polynomialMoment_criticalMildPathIntegrand_add_half_le
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.criticalMildDuhamelTail_polynomialMoment_add_half
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.exists_uniform_polynomialMoment_add_half_on_compactPositiveInterval
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.uniform_iteratedHalfOrder_on_nestedPositiveIntervals
#print axioms Navier.Analysis.CriticalMildHigherUniformMoments.exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
