import Navier.Analysis.PeriodicMildClassicalRealization
import Navier.Routes.R7.FiniteReality

/-!
# Reality preservation for the literal critical mild convolution

Raw amplitudes use the normalization `A = -2πi û`, so real physical Fourier
data are anti-Hermitian.  This module proves the corresponding sign law for
the actual countable lattice convolution rather than a finite surrogate.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildRealityPreservation

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Routes.R7

@[simp] theorem latticeFrequency_neg (k : LatticeMode) :
    latticeFrequency (-k) = -latticeFrequency k := by
  ext i
  fin_cases i <;> simp [latticeFrequency]

/-- Negating both inputs in the anti-Hermitian raw normalization leaves one
minus sign after conjugating the bilinear transport coefficient. -/
theorem spectralTransport_neg_antiHermitian
    (q : Space) (a b : ComplexSpace) :
    spectralTransport (-q) (-complexConjugate a) (-complexConjugate b) =
      -complexConjugate (spectralTransport q a b) := by
  unfold spectralTransport
  ext i
  simp [complexConjugate, complexFrequency, complexEuclideanPoint,
    complexOfReal, complexOfParts, PiLp.inner_apply, RCLike.inner_apply,
    map_sum]

private def negPairEquiv :
    (LatticeMode × LatticeMode) ≃ (LatticeMode × LatticeMode) :=
  (Equiv.neg LatticeMode).prodCongr (Equiv.neg LatticeMode)

@[simp] private theorem negPairEquiv_apply (ij : LatticeMode × LatticeMode) :
    negPairEquiv ij = (-ij.1, -ij.2) := rfl

private theorem latticeSpectralTerm_neg_pair
    {u v : WeightedLatticeBanach}
    (hu : LatticeAntiHermitian u) (hv : LatticeAntiHermitian v)
    (k : LatticeMode) (ij : LatticeMode × LatticeMode) :
    WithLp.ofLp (latticeSpectralTerm (-k)
      (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
      (negPairEquiv ij)) =
      -complexConjugate (WithLp.ofLp (latticeSpectralTerm k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient v) ij)) := by
  by_cases hij : ij.1 + ij.2 = k
  · have hneg : (-ij.1) + (-ij.2) = -k := by rw [← neg_add, hij]
    simp only [latticeSpectralTerm, negPairEquiv_apply, hneg, hij, if_true]
    rw [latticeFrequency_neg, hu ij.1, hv ij.2,
      spectralTransport_neg_antiHermitian]
    ext i
    rfl
  · have hneg : ¬(-ij.1) + (-ij.2) = -k := by
      intro h
      apply hij
      simpa only [← neg_add, neg_inj] using h
    simp only [latticeSpectralTerm, negPairEquiv_apply, hneg, hij, if_false,
      WithLp.ofLp_zero]
    ext i
    simp [complexConjugate]

/-- The literal absolutely convergent weighted lattice convolution obeys the
raw anti-Hermitian sign law. -/
theorem spectralOutputCoefficient_neg_antiHermitian
    {u v : WeightedLatticeBanach}
    (hu : LatticeAntiHermitian u) (hv : LatticeAntiHermitian v)
    (k : LatticeMode) :
    spectralOutputCoefficient (-k) u v =
      -complexConjugate (spectralOutputCoefficient k u v) := by
  ext i
  let term := fun q ij => latticeSpectralTerm q
    (weightedLatticeCoefficient u) (weightedLatticeCoefficient v) ij
  have hsumNeg : Summable (term (-k)) :=
    summable_latticeSpectralTerm_of_weightedL1 (-k) _ _
      (latticeConvolutionWeightedL1_of_weightedL1 (-k) _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v))
  have hsum : Summable (term k) :=
    summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v))
  change complexE3CoordinateCLM i (∑' ij, term (-k) ij) =
    -star (complexE3CoordinateCLM i (∑' ij, term k ij))
  rw [(complexE3CoordinateCLM i).map_tsum hsumNeg,
    (complexE3CoordinateCLM i).map_tsum hsum, tsum_star, ← tsum_neg]
  calc
    (∑' ij, complexE3CoordinateCLM i (term (-k) ij)) =
        ∑' ij, complexE3CoordinateCLM i (term (-k) (negPairEquiv ij)) :=
      (negPairEquiv.tsum_eq (fun ij => complexE3CoordinateCLM i (term (-k) ij))).symm
    _ = ∑' ij, -star (complexE3CoordinateCLM i (term k ij)) := by
      apply tsum_congr
      intro ij
      have h := congrArg (fun z : ComplexSpace => z i)
        (latticeSpectralTerm_neg_pair hu hv k ij)
      simpa [term, complexE3CoordinateCLM, complexConjugate] using h

/-- Heat and Leray preserve the raw sign law at the negated frequency. -/
theorem complexFrequencyHeatLeray_neg_antiHermitian
    (ν τ : ℝ) (q : Space) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν τ (-q) (-complexConjugate z) =
      -complexConjugate (complexFrequencyHeatLeray ν τ q z) := by
  have hdecay : complexHeatDecay ν τ (-q) = complexHeatDecay ν τ q := by
    simp [complexHeatDecay, FrequencyHeatLeray.heatDecay,
      OfficialABEncoding.officialEuclideanPoint]
  have heven (w : ComplexSpace) :
      complexFrequencyHeatLeray ν τ (-q) w =
        complexFrequencyHeatLeray ν τ q w := by
    rw [complexFrequencyHeatLeray_apply, complexFrequencyHeatLeray_apply,
      hdecay, complexLeray_neg_frequency]
  rw [map_neg, heven, complexFrequencyHeatLeray_conjugate]

/-- The actual completed heat-regularized nonlinear output preserves raw
anti-Hermitian reality. -/
theorem heatRegularizedSpectralOutput_antiHermitian
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    {u v : WeightedLatticeBanach}
    (hu : LatticeAntiHermitian u) (hv : LatticeAntiHermitian v)
    (hdiv : LatticeDivergenceFree u) :
    LatticeAntiHermitian
      (heatRegularizedSpectralOutput ν τ hν hτ u v hdiv) := by
  intro k
  rw [weightedLatticeCoefficient_heatRegularizedSpectralOutput,
    weightedLatticeCoefficient_heatRegularizedSpectralOutput,
    latticeFrequency_neg, spectralOutputCoefficient_neg_antiHermitian hu hv]
  exact complexFrequencyHeatLeray_neg_antiHermitian ν τ
    (latticeFrequency k) (spectralOutputCoefficient k u v)

/-- The zero-extended heat output preserves reality for every real lag. -/
theorem positiveTimeHeatRegularizedSpectralOutput_antiHermitian
    (ν : ℝ) (hν : 0 < ν) {u v : WeightedLatticeBanach}
    (hu : LatticeAntiHermitian u) (hv : LatticeAntiHermitian v)
    (hdiv : LatticeDivergenceFree u) (τ : ℝ) :
    LatticeAntiHermitian
      (positiveTimeHeatRegularizedSpectralOutput ν hν u v hdiv τ) := by
  by_cases hτ : 0 < τ
  · rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hdiv hτ]
    exact heatRegularizedSpectralOutput_antiHermitian ν τ hν hτ hu hv hdiv
  · have hz : positiveTimeHeatRegularizedSpectralOutput ν hν u v hdiv τ = 0 := by
      simp [positiveTimeHeatRegularizedSpectralOutput, hτ]
    rw [hz]
    intro k
    rw [show weightedLatticeCoefficient (0 : WeightedLatticeBanach) (-k) = 0 by
      simp [weightedLatticeCoefficient],
      show weightedLatticeCoefficient (0 : WeightedLatticeBanach) k = 0 by
        simp [weightedLatticeCoefficient]]
    ext i
    simp [complexConjugate]

/-- Consumer on the literal evolving-path mild integrand. -/
theorem criticalMildPathIntegrand_antiHermitian
    (ν : ℝ) (hν : 0 < ν) (u : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ s, LatticeDivergenceFree (u s))
    (hreal : ∀ s, LatticeAntiHermitian (u s)) (t s : ℝ) :
    LatticeAntiHermitian (criticalMildPathIntegrand ν hν u hdiv t s) := by
  exact positiveTimeHeatRegularizedSpectralOutput_antiHermitian
    ν hν (hreal s) (hreal s) (hdiv s) (t - s)

end Navier.Analysis.CriticalMildRealityPreservation
