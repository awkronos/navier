import Navier.Analysis.CriticalMildHigherUniformMoments
import Navier.Analysis.PeriodicMildClassicalRealization
import Navier.Construction.ParametricKernelBounds
import Navier.Construction.PhysicalGraphBounds

/-!
# Positive-time spatial smoothness of the periodic mild reconstruction

The actual critical mild trajectory has every finite polynomial Fourier moment
at positive time.  This file converts that coefficient-side statement into
`C∞` spatial regularity of its period-one Fourier reconstruction.  The estimate
uses the exact character `exp (2π i k · x)` and a summable majorant at every
Fréchet derivative order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ContDiff
open Set

namespace Navier.Analysis.PeriodicSpatialSmoothReconstruction

open Navier
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Construction.ParametricKernelBounds
open Navier.Construction.PhysicalGraphBounds

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

private theorem character_comp_positive_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (x : E) (m : ℕ) {c B M : ℝ}
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (character c ∘ Φ) x‖ ≤
        (m.factorial : ℝ) * M ^ m * B ^ m := by
  intro k hk
  have he := norm_iteratedFDeriv_comp_le (character_smooth c) hΦ
    (nat_le_smooth k) x (C := M ^ m) (D := B)
    (fun i hi => by
      rw [norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans
        (pow_le_pow_right₀ hM (hi.trans hk)))
    (fun i hi hik => (hΦb i hi (hik.trans hk)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hB hi))
  exact he.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.factorial_le hk) (by positivity))
    (pow_le_pow_right₀ hB hk) (by positivity) (by positivity))

/-- The continuous linear phase `k · x` underlying the exact period-one
lattice character.  The official spatial norm is the product sup norm, so the
phase is written as a finite sum of coordinate projections. -/
def latticePhaseCLM (m : LatticeMode) : Space →L[ℝ] ℝ :=
  ∑ i : Fin 3,
    (latticeFrequency m i) •
      (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ)

def latticePhase (m : LatticeMode) : Space → ℝ := latticePhaseCLM m

theorem latticePhase_apply (m : LatticeMode) (x : Space) :
    latticePhase m x = ∑ i : Fin 3, latticeFrequency m i * x i := by
  simp [latticePhase, latticePhaseCLM]

theorem latticePhase_contDiff (m : LatticeMode) :
    ContDiff ℝ ∞ (latticePhase m) :=
  (latticePhaseCLM m).contDiff

theorem norm_latticePhaseCLM_le (m : LatticeMode) :
    ‖latticePhaseCLM m‖ ≤ 3 * latticeModeWeight m := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (by norm_num)
      (zero_le_one.trans (one_le_latticeModeWeight m))
  intro x
  rw [show latticePhaseCLM m x = latticePhase m x by rfl,
    latticePhase_apply]
  calc
    ‖∑ i : Fin 3, latticeFrequency m i * x i‖ ≤
        ∑ i : Fin 3, ‖latticeFrequency m i * x i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, latticeModeWeight m * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul]
      exact mul_le_mul
        (by simpa only [Real.norm_eq_abs, Complex.norm_real] using
          norm_latticeFrequency_coordinate_le_weight m i)
        (norm_le_pi_norm x i) (norm_nonneg _)
        (zero_le_one.trans (one_le_latticeModeWeight m))
    _ = (3 * latticeModeWeight m) * ‖x‖ := by
      simp
      ring

theorem latticeCharacter_eq_character_comp_latticePhase
    (m : LatticeMode) :
    latticeCharacter m = character (2 * Real.pi) ∘ latticePhase m := by
  funext x
  rw [latticeCharacter_eq_exp]
  simp only [Function.comp_apply, character, phaseFactor, latticePhase_apply,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  unfold periodOneDerivative
  push_cast
  ring

/-- Every order-`n` Fréchet derivative of the exact lattice character is
bounded by the order-`n` polynomial Fourier weight.  The numerical constants
come only from `2π` and comparison of the official sup norm with the three
coordinate phase. -/
theorem norm_iteratedFDeriv_latticeCharacter_le
    (n : ℕ) (m : LatticeMode) (x : Space) :
    ‖iteratedFDeriv ℝ n (latticeCharacter m) x‖ ≤
      (n.factorial : ℝ) * 8 ^ n *
        (3 * latticeModeWeight m) ^ n := by
  rw [latticeCharacter_eq_character_comp_latticePhase m]
  have hB : 1 ≤ 3 * latticeModeWeight m :=
    le_trans (by norm_num) (mul_le_mul_of_nonneg_left
      (one_le_latticeModeWeight m) (by norm_num))
  have hc : |(2 : ℝ) * Real.pi| ≤ 8 := by
    rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_lt_four]
  have hphase : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (latticePhase m) x‖ ≤
        3 * latticeModeWeight m := by
    intro i hi _hin
    have hlinear :=
      norm_iteratedFDeriv_linear_le (latticePhaseCLM m) i hi x
    simpa only [latticePhase] using
      hlinear.trans (norm_latticePhaseCLM_le m)
  exact character_comp_positive_jets (latticePhase_contDiff m) x n
    hB (by norm_num) hc hphase n le_rfl

theorem contDiff_latticeCharacter (m : LatticeMode) :
    ContDiff ℝ ∞ (latticeCharacter m) := by
  rw [latticeCharacter_eq_character_comp_latticePhase m]
  exact (character_smooth (2 * Real.pi)).comp (latticePhase_contDiff m)

theorem contDiff_latticeFourierTerm (u : WeightedLatticeBanach)
    (m : LatticeMode) :
    ContDiff ℝ ∞ (latticeFourierTerm u m) := by
  unfold latticeFourierTerm
  exact (contDiff_latticeCharacter m).smul_const _

/-- A summable majorant for the order-`n` derivative of every Fourier mode. -/
def spatialJetMajorant (n : ℕ) (u : WeightedLatticeBanach)
    (m : LatticeMode) : ℝ :=
  (n.factorial : ℝ) * 8 ^ n * 3 ^ n *
    polynomialMomentAmplitude n u m

theorem summable_spatialJetMajorant (n : ℕ) (u : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment n u) :
    Summable (spatialJetMajorant n u) := by
  exact hu.mul_left ((n.factorial : ℝ) * 8 ^ n * 3 ^ n)

theorem norm_iteratedFDeriv_latticeFourierTerm_le
    (n : ℕ) (u : WeightedLatticeBanach) (m : LatticeMode) (x : Space) :
    ‖iteratedFDeriv ℝ n (latticeFourierTerm u m) x‖ ≤
      spatialJetMajorant n u m := by
  let v : ComplexE3 :=
    complexEuclideanPoint (weightedLatticeCoefficient u m)
  let L : ℂ →L[ℝ] ComplexE3 :=
    (ContinuousLinearMap.id ℝ ℂ).smulRight v
  have hL : ‖L‖ ≤ ‖v‖ := by
    refine L.opNorm_le_bound (norm_nonneg v) ?_
    intro z
    simp only [L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
    rw [norm_smul]
    rw [mul_comm]
  have hderiv :
      ‖iteratedFDeriv ℝ n (latticeFourierTerm u m) x‖ ≤
        ‖v‖ * ‖iteratedFDeriv ℝ n (latticeCharacter m) x‖ := by
    unfold latticeFourierTerm
    rw [iteratedFDeriv_smul_const_apply
      ((contDiff_latticeCharacter m).contDiffAt.of_le (nat_le_smooth n))]
    exact (L.norm_compContinuousMultilinearMap_le
      (iteratedFDeriv ℝ n (latticeCharacter m) x)).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    ‖iteratedFDeriv ℝ n (latticeFourierTerm u m) x‖ ≤
        ‖v‖ * ((n.factorial : ℝ) * 8 ^ n *
          (3 * latticeModeWeight m) ^ n) :=
      hderiv.trans (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_latticeCharacter_le n m x) (norm_nonneg v))
    _ = spatialJetMajorant n u m := by
      unfold spatialJetMajorant polynomialMomentAmplitude v
      rw [mul_pow, Real.rpow_natCast]
      change complexEuclideanNorm (weightedLatticeCoefficient u m) *
          ((n.factorial : ℝ) * 8 ^ n *
            (3 ^ n * latticeModeWeight m ^ n)) = _
      ring

/-- All polynomial Fourier moments imply spatial `C∞` regularity of the
literal complex period-one reconstruction. -/
theorem contDiff_complexFourierReconstruction_of_allMoments
    (u : WeightedLatticeBanach)
    (hu : ∀ n : ℕ, LatticePolynomialMoment n u) :
    ContDiff ℝ ∞ (complexFourierReconstruction u) := by
  unfold complexFourierReconstruction
  exact contDiff_tsum
    (fun m => contDiff_latticeFourierTerm u m)
    (fun n _hn => summable_spatialJetMajorant n u (hu n))
    (fun n m x _hn => norm_iteratedFDeriv_latticeFourierTerm_le n u m x)

/-- Taking coordinatewise real parts preserves the spatial smoothness of the
actual physical Fourier reconstruction. -/
theorem contDiff_physicalFourierReconstruction_of_allMoments
    (u : WeightedLatticeBanach)
    (hu : ∀ n : ℕ, LatticePolynomialMoment n u) :
    ContDiff ℝ ∞ (physicalFourierReconstruction u) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ ∞ (fun x : Space =>
    Complex.reCLM (complexE3CoordinateCLM i
      (complexFourierReconstruction u x)))
  exact Complex.reCLM.contDiff.comp
    (((complexE3CoordinateCLM i).restrictScalars ℝ).contDiff.comp
      (contDiff_complexFourierReconstruction_of_allMoments u hu))

theorem latticePolynomialMoment_physicalCarrier
    (p : ℝ) (A : WeightedLatticeBanach)
    (hA : LatticePolynomialMoment p A) :
    LatticePolynomialMoment p (physicalCarrier A) := by
  have hscaled := hA.mul_left ‖rawToPhysicalAmplitude‖
  apply hscaled.congr
  intro k
  unfold polynomialMomentAmplitude physicalCarrier complexEuclideanNorm
  rw [congrFun (weightedLatticeCoefficient_smul rawToPhysicalAmplitude A) k,
    Pi.smul_apply, complexEuclideanPoint_smul, norm_smul]
  ring

theorem iteratedHalfOrder_eq (p : ℝ) (n : ℕ) :
    iteratedHalfOrder p n = p + (n : ℝ) / 2 := by
  induction n with
  | zero => simp [iteratedHalfOrder]
  | succ n ih =>
      rw [iteratedHalfOrder, ih]
      push_cast
      ring

/-- The checked all-moment bootstrap for the actual bounded mild trajectory
therefore produces a spatially `C∞` physical velocity at every positive time
in its chart. -/
theorem contDiff_physicalMildVelocity_at_positiveTime
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R T : ℝ} (hR : 0 ≤ R)
    (huR : ∀ x ∈ Ioc (0 : ℝ) T, ‖u x‖ ≤ R)
    (hmild : ∀ x (hx : x ∈ Icc (0 : ℝ) T),
      u x = criticalMildImage
        ν hν u₀ u hu x hx.1)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ContDiff ℝ ∞ (physicalMildVelocity u t) := by
  obtain ⟨B, _hB, hall⟩ :=
    exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
      ν hν u₀ hu₀ u huc hu hR ht htT huR hmild
  rw [physicalMildVelocity,
    reconstructedVelocity_eq_physicalFourierReconstruction]
  apply contDiff_physicalFourierReconstruction_of_allMoments
  intro n
  apply latticePolynomialMoment_physicalCarrier
  have hhigh := (hall (2 * n) t ⟨le_rfl, htT⟩).1
  exact latticePolynomialMoment_mono (u := u t) (hu := hhigh) (by
    rw [iteratedHalfOrder_eq]
    push_cast
    norm_num)

end Navier.Analysis.PeriodicSpatialSmoothReconstruction
