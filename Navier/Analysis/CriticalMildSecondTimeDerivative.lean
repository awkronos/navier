import Navier.Analysis.CriticalMildTimeJetInterchange

/-!
# Second time derivative of the actual periodic mild trajectory

This module differentiates the literal projected convolution through its
continuous bilinear carrier map.  It consumes the first strong carrier
derivative constructed from positive-time spatial smoothing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal
open Set

namespace Navier.Analysis.CriticalMildSecondTimeDerivative

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

/-- The derivative of the projected quadratic forcing along a carrier
direction.  Both slots of the literal countable convolution are present. -/
def projectedModeForcingCarrierDerivative
    (A V : WeightedLatticeBanach) (k : LatticeMode) : ComplexSpace :=
  WithLp.ofLp (complexEuclideanLeray (latticeFrequency k)
    (weightedLatticeSpectralBilinear k V A +
      weightedLatticeSpectralBilinear k A V))

private def complexEuclideanCoordinatesCLMReal :
    ComplexE3 →L[ℝ] ComplexSpace :=
  (ContinuousLinearEquiv.toContinuousLinearMap
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ))).restrictScalars ℝ

@[simp] private theorem complexEuclideanCoordinatesCLMReal_apply
    (z : ComplexE3) :
    complexEuclideanCoordinatesCLMReal z = WithLp.ofLp z := rfl

/-- Differentiating the actual projected forcing uses the two Leibniz terms
of the completed bilinear convolution. -/
theorem hasDerivAt_projectedModeForcing_of_hasDerivAt
    (A : ℝ → WeightedLatticeBanach) {t : ℝ}
    (V : WeightedLatticeBanach) (hA : HasDerivAt A V t)
    (k : LatticeMode) :
    HasDerivAt (projectedModeForcing A k)
      (projectedModeForcingCarrierDerivative (A t) V k) t := by
  let B := (weightedLatticeSpectralBilinear k).bilinearRestrictScalars ℝ
  have hconv : HasDerivAt (fun r => B (A r) (A r))
      (B (A t) V + B V (A t)) t :=
    B.hasDerivAt_of_bilinear (fun _ => hA) (fun _ => hA)
  let P := (complexEuclideanLeray (latticeFrequency k)).restrictScalars ℝ
  have hproj : HasDerivAt (fun r => P (B (A r) (A r)))
      (P (B (A t) V + B V (A t))) t :=
    P.hasFDerivAt.comp_hasDerivAt t hconv
  have hdecode : HasDerivAt
      (fun r => complexEuclideanCoordinatesCLMReal (P (B (A r) (A r))))
      (complexEuclideanCoordinatesCLMReal
        (P (B (A t) V + B V (A t)))) t :=
    complexEuclideanCoordinatesCLMReal.hasFDerivAt.comp_hasDerivAt t hproj
  convert hdecode using 1
  · funext r
    unfold projectedModeForcing spectralOutputCoefficient
    apply complexEuclideanPoint_injective
    rw [complexEuclideanPoint_complexLeray]
    change complexEuclideanLeray (latticeFrequency k)
      (weightedLatticeSpectralBilinear k (A r) (A r)) =
        complexEuclideanLeray (latticeFrequency k)
          (weightedLatticeSpectralBilinear k (A r) (A r))
    rfl
  · unfold projectedModeForcingCarrierDerivative
    simp [B, P, add_comm]

/-- The second raw time derivative at a mode: the two differentiated
convolution slots minus the heat-generator action on the first derivative. -/
def mildRawSecondTimeDerivative
    (μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) (k : LatticeMode) : ComplexSpace :=
  projectedModeForcingCarrierDerivative (A t) V k -
    (rawModeDecayRate μ k : ℂ) • mildRawTimeDerivative μ A t k

/-- Once the first carrier derivative has been constructed, the actual mode
ODE differentiates a second time with the literal quadratic Leibniz rule. -/
theorem hasDerivAt_mildRawTimeDerivative
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (V : WeightedLatticeBanach) (hA : HasDerivAt A V t)
    (k : LatticeMode) :
    HasDerivAt (fun r => mildRawTimeDerivative μ A r k)
      (mildRawSecondTimeDerivative μ A V t k) t := by
  have hforce := hasDerivAt_projectedModeForcing_of_hasDerivAt A V hA k
  have hcoefficient : HasDerivAt
      (fun r => weightedLatticeCoefficient (A r) k)
      (mildRawTimeDerivative μ A t k) t := by
    rw [hasDerivAt_pi]
    intro i
    exact hasDerivAt_mildPath_coefficient_eq_mildRawTimeDerivative
      μ hμ u₀ A hAc hdiv hR ht hbound hmild k i
  unfold mildRawTimeDerivative mildRawSecondTimeDerivative
  exact hforce.sub (hcoefficient.const_smul (rawModeDecayRate μ k : ℂ))

/-- **Actual second time derivative, mode by mode.** Positive-time spatial
smoothing first constructs the strong derivative `V` in the completed
carrier.  Differentiating the genuine bilinear forcing along that same `V`
then supplies the displayed second derivative for every lattice mode. -/
theorem exists_firstCarrierDerivative_and_secondModeDerivative
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T t : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (ht : t ∈ Ioo a T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1) :
    ∃ (hD : TimeDerivativePolynomialMoment 1
          (mildRawTimeDerivative μ A t))
        (V : WeightedLatticeBanach),
      V = weightedTimeDerivativeCarrier
          (mildRawTimeDerivative μ A t) hD ∧
      HasDerivAt A V t ∧
      ∀ k, HasDerivAt (fun r => mildRawTimeDerivative μ A r k)
        (mildRawSecondTimeDerivative μ A V t k) t := by
  obtain ⟨hD, hA⟩ :=
    exists_hasDerivAt_mildPath_in_weightedCarrier
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT hbound hmild t ht
  let V := weightedTimeDerivativeCarrier
    (mildRawTimeDerivative μ A t) hD
  refine ⟨hD, V, rfl, hA, ?_⟩
  intro k
  exact hasDerivAt_mildRawTimeDerivative
    μ hμ u₀ A hAc hdiv hR ⟨ha.trans ht.1, ht.2⟩
      hbound hmild V hA k

end Navier.Analysis.CriticalMildSecondTimeDerivative

#print axioms Navier.Analysis.CriticalMildSecondTimeDerivative.hasDerivAt_projectedModeForcing_of_hasDerivAt
#print axioms Navier.Analysis.CriticalMildSecondTimeDerivative.hasDerivAt_mildRawTimeDerivative
#print axioms Navier.Analysis.CriticalMildSecondTimeDerivative.exists_firstCarrierDerivative_and_secondModeDerivative
