import Navier.Analysis.CriticalMildTimeJetInterchange
import Navier.Analysis.PeriodicNonlinearFourierReconstruction

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal
open Set

namespace Navier.Analysis.PeriodicMildTimeDerivativeReconstruction

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildTimeJetInterchange
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicNonlinearFourierReconstruction
open Navier.Analysis.PeriodicPressureRecovery

theorem complexFourierReconstruction_add
    (u v : WeightedLatticeBanach) (x : Space) :
    complexFourierReconstruction (u + v) x =
      complexFourierReconstruction u x + complexFourierReconstruction v x := by
  unfold complexFourierReconstruction
  rw [← (summable_latticeFourierTerm u x).tsum_add
    (summable_latticeFourierTerm v x)]
  apply tsum_congr
  intro k
  simp [latticeFourierTerm, weightedLatticeCoefficient_add,
    complexEuclideanPoint, smul_add]

theorem complexFourierReconstruction_smul
    (c : ℂ) (u : WeightedLatticeBanach) (x : Space) :
    complexFourierReconstruction (c • u) x =
      c • complexFourierReconstruction u x := by
  unfold complexFourierReconstruction
  rw [← Summable.tsum_const_smul c (summable_latticeFourierTerm u x)]
  apply tsum_congr
  intro k
  simp [latticeFourierTerm, weightedLatticeCoefficient_smul,
    complexEuclideanPoint, smul_smul, mul_comm]

/-- Evaluation of the actual complex Fourier reconstruction is a bounded
complex-linear map on the completed critical carrier. -/
def complexFourierEvaluationCLM (x : Space) :
    WeightedLatticeBanach →L[ℂ] ComplexE3 :=
  LinearMap.mkContinuous
    { toFun := fun u => complexFourierReconstruction u x
      map_add' := fun u v => complexFourierReconstruction_add u v x
      map_smul' := fun c u => complexFourierReconstruction_smul c u x }
    1 (fun u => by simpa using norm_complexFourierReconstruction_le u x)

@[simp] theorem complexFourierEvaluationCLM_apply
    (x : Space) (u : WeightedLatticeBanach) :
    complexFourierEvaluationCLM x u = complexFourierReconstruction u x := rfl

/-- The actual physical decoder followed by Fourier evaluation and real-part
extraction, as a bounded real-linear map. -/
def physicalFourierEvaluationCLM (x : Space) :
    WeightedLatticeBanach →L[ℝ] Space :=
  let decode : WeightedLatticeBanach →L[ℂ] WeightedLatticeBanach :=
    (ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] (WeightedLatticeBanach →L[ℂ] WeightedLatticeBanach))
        rawToPhysicalAmplitude
  let complexEval : WeightedLatticeBanach →L[ℝ] ComplexE3 :=
    (complexFourierEvaluationCLM x).restrictScalars ℝ
  let realPart : ComplexE3 →L[ℝ] Space :=
    ContinuousLinearMap.pi fun i => Complex.reCLM.comp
      ((complexE3CoordinateCLM i).restrictScalars ℝ)
  realPart.comp (complexEval.comp (decode.restrictScalars ℝ))

@[simp] theorem physicalFourierEvaluationCLM_apply
    (x : Space) (u : WeightedLatticeBanach) :
    physicalFourierEvaluationCLM x u =
      physicalFourierReconstruction (physicalCarrier u) x := by
  ext i
  simp [physicalFourierEvaluationCLM, physicalFourierReconstruction,
    physicalCarrier]
  rw [complexFourierReconstruction_smul]
  rfl

/-- A strong derivative of the raw carrier reconstructs to the strong time
derivative of the actual physical velocity at every spatial point. -/
theorem hasDerivAt_physicalMildVelocity_of_hasDerivAt_carrier
    {A : ℝ → WeightedLatticeBanach} {V : WeightedLatticeBanach}
    {t : ℝ} (hA : HasDerivAt A V t) (x : Space) :
    HasDerivAt (fun s => physicalMildVelocity A s x)
      (physicalFourierReconstruction (physicalCarrier V) x) t := by
  have h := (physicalFourierEvaluationCLM x).hasFDerivAt.comp_hasDerivAt t hA
  have hfun : (physicalFourierEvaluationCLM x) ∘ A =
      fun s => physicalMildVelocity A s x := by
    funext s
    simp only [Function.comp_apply, physicalMildVelocity,
      reconstructedVelocity_eq_physicalFourierReconstruction,
      physicalFourierEvaluationCLM_apply]
  rw [hfun] at h
  exact h

/-- Reconstructing the encoded derivative carrier gives exactly the physical
raw-mode derivative series used in `PhysicalPointwiseFourierBalance`. -/
theorem physicalFourierReconstruction_weightedTimeDerivativeCarrier
    (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D)
    (x : Space) (i : Fin 3) :
    physicalFourierReconstruction
        (physicalCarrier (weightedTimeDerivativeCarrier D hD)) x i =
      (complexCoefficientSeriesCoordinate
        (fun k => rawToPhysicalAmplitude • D k) x i).re := by
  unfold physicalFourierReconstruction complexCoefficientSeriesCoordinate
  rw [complexFourierReconstruction_apply_eq]
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  rw [show weightedLatticeCoefficient
      (physicalCarrier (weightedTimeDerivativeCarrier D hD)) k =
        rawToPhysicalAmplitude • D k by
    unfold physicalCarrier
    rw [congrFun (weightedLatticeCoefficient_smul rawToPhysicalAmplitude
      (weightedTimeDerivativeCarrier D hD)) k, Pi.smul_apply,
      weightedLatticeCoefficient_weightedTimeDerivativeCarrier]]

/-- At positive time, an ordinary strong derivative identifies the official
one-sided `timeDerivative`; no smoothness premise is needed. -/
theorem timeDerivative_eq_of_hasDerivAt_physicalMildVelocity
    {A : ℝ → WeightedLatticeBanach} {V : WeightedLatticeBanach}
    {t : ℝ} (ht : 0 < t) (hA : HasDerivAt A V t) (x : Space) :
    timeDerivative (physicalMildVelocity A) t x =
      physicalFourierReconstruction (physicalCarrier V) x := by
  have h := hasDerivAt_physicalMildVelocity_of_hasDerivAt_carrier hA x
  have hnhds : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
  unfold timeDerivative
  rw [fderivWithin_of_mem_nhds hnhds, h.hasFDerivAt.fderiv]
  simp

/-- The actual bounded mild trajectory's strong carrier derivative removes
the abstract time term from the physical pointwise Fourier balance. -/
theorem timeDerivative_physicalMildVelocity_eq_rawSeries
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1) :
    ∀ t ∈ Ioo a T, ∀ x : Space, ∀ i : Fin 3,
      timeDerivative (physicalMildVelocity A) t x i =
        (complexCoefficientSeriesCoordinate
          (fun k => rawToPhysicalAmplitude •
            mildRawTimeDerivative μ A t k) x i).re := by
  intro t ht x i
  obtain ⟨hD, hstrong⟩ :=
    exists_hasDerivAt_mildPath_in_weightedCarrier
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT hbound hmild t ht
  have htime := timeDerivative_eq_of_hasDerivAt_physicalMildVelocity
    (ha.trans ht.1) hstrong x
  exact congrFun htime i |>.trans
    (physicalFourierReconstruction_weightedTimeDerivativeCarrier
      (mildRawTimeDerivative μ A t) hD x i)

/-- The complex Fourier balance of an actual mild trajectory now has the
repository's official time derivative as its first real term.  The remaining
three terms are the spatial convection, viscous, and pressure reconstructions;
their identification with the corresponding Fréchet operators is deliberately
separate. -/
theorem physicalPointwiseFourierBalance_to_officialTimeDerivative
    (nu : ℝ) (hnu : 0 < nu)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T t : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage (rawMildViscosity nu)
        (by unfold rawMildViscosity; positivity) u₀ A hdiv s hs.1)
    (ht : t ∈ Ioo a T) (x : Space) (i : Fin 3)
    (hbalance : PhysicalPointwiseFourierBalance nu A t x i) :
    timeDerivative (physicalMildVelocity A) t x i +
        (complexPointwiseConvection (physicalCarrier (A t)) x i).re +
        (complexCoefficientSeriesCoordinate
          (fun k => periodOneViscousCoefficient nu k
            (weightedLatticeCoefficient (physicalCarrier (A t)) k)) x i).re +
        (complexPressureGradientReconstruction
          (physicalCarrier (A t)) x i).re = 0 := by
  have hμ : 0 < rawMildViscosity nu := by
    unfold rawMildViscosity
    positivity
  have htime := timeDerivative_physicalMildVelocity_eq_rawSeries
    (rawMildViscosity nu) hμ u₀ hu₀ A hAc hdiv hR ha haT
      hbound hmild t ht x i
  have hreal := congrArg Complex.re hbalance
  simp only [Complex.add_re, Complex.zero_re] at hreal
  rw [← htime] at hreal
  exact hreal

end Navier.Analysis.PeriodicMildTimeDerivativeReconstruction
