import Navier.Analysis.PhysicalLocalEvolution
import Navier.Analysis.CriticalMildPolynomialMomentConvolution

/-!
# Official periodic data enter the physical local evolution

Smooth periodic native data have every polynomial Fourier moment.  Their
literal coefficients are then rotated by `-2πi` into the raw mild carrier and
fed to the constructed physical local evolution without projecting or
replacing the datum.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Navier.Analysis.PeriodicInitialPhysicalEvolution

open Set
open scoped BigOperators ContDiff
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.CriticalMildHigherMomentBootstrap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.PeriodicDatumFourierBridge
open Navier.Analysis.PeriodicDatumFourierConstraints
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PhysicalLocalEvolution
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.OfficialABEncoding
open Navier.Construction

/-- Arbitrary product-frequency decay from smoothness, including the zero
slice of the first lattice coordinate. -/
theorem exists_scalarCoefficient_productBound_at {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : LatticeMode,
      (1 + |(k.1 : ℝ)|) ^ r * TorusInverse.weight k.2 ^ s *
        ‖scalarCoefficient f k‖ ≤ C := by
  obtain ⟨C₀, hC₀, hzero⟩ := exists_parameterJet_planeBound hf hp 0 s
  obtain ⟨C₁, hC₁, hnonzero⟩ := exists_scalarCoefficient_mixedBound hf hp r s
  refine ⟨max C₀ ((2 : ℝ) ^ r * C₁), hC₀.trans (le_max_left _ _), ?_⟩
  intro k
  by_cases hk : k.1 = 0
  · have hunit : ‖scalarCoefficient f k‖ ≤
        C₀ / TorusInverse.weight k.2 ^ s := by
      change ‖SmoothFourierData.unitCoeff
        (fun z => ParametricTorusInverse.coefficient f z k.2) k.1‖ ≤ _
      apply SmoothFourierData.unitCoeff_norm_le
      intro z hz
      exact (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) s)).2
        (by simpa [ParametricTorusInverse.parameterJet, mul_comm] using hzero z hz k)
    have hplane : TorusInverse.weight k.2 ^ s * ‖scalarCoefficient f k‖ ≤ C₀ := by
      simpa [mul_comm] using
        (le_div_iff₀ (pow_pos (TorusInverse.weight_pos k.2) s)).1 hunit
    rw [hk]
    simpa using hplane.trans (le_max_left _ _)
  · have habs : (1 : ℝ) ≤ |(k.1 : ℝ)| := by
      have hn : 1 ≤ k.1.natAbs :=
        (Nat.one_le_iff_ne_zero).2 ((Int.natAbs_ne_zero).2 hk)
      calc
        (1 : ℝ) ≤ (k.1.natAbs : ℝ) := by exact_mod_cast hn
        _ = |(k.1 : ℝ)| := by
          rw [← Int.cast_abs]
          exact congrArg (fun z : ℤ => (z : ℝ))
            (Int.natCast_natAbs k.1)
    have hone : 1 + |(k.1 : ℝ)| ≤ 2 * |(k.1 : ℝ)| := by linarith
    have hpow : (1 + |(k.1 : ℝ)|) ^ r ≤
        (2 : ℝ) ^ r * |(k.1 : ℝ)| ^ r := by
      calc
        (1 + |(k.1 : ℝ)|) ^ r ≤ (2 * |(k.1 : ℝ)|) ^ r :=
          pow_le_pow_left₀ (by positivity) hone r
        _ = (2 : ℝ) ^ r * |(k.1 : ℝ)| ^ r := mul_pow _ _ _
    calc
      (1 + |(k.1 : ℝ)|) ^ r * TorusInverse.weight k.2 ^ s *
          ‖scalarCoefficient f k‖ ≤
        ((2 : ℝ) ^ r * |(k.1 : ℝ)| ^ r) *
          TorusInverse.weight k.2 ^ s * ‖scalarCoefficient f k‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow
                (pow_nonneg (TorusInverse.weight_pos k.2).le s))
              (norm_nonneg _)
      _ = (2 : ℝ) ^ r *
          (|(k.1 : ℝ)| ^ r * TorusInverse.weight k.2 ^ s *
            ‖scalarCoefficient f k‖) := by ring
      _ ≤ (2 : ℝ) ^ r * C₁ :=
        mul_le_mul_of_nonneg_left (hnonzero k hk) (by positivity)
      _ ≤ max C₀ ((2 : ℝ) ^ r * C₁) := le_max_right _ _

/-- Every natural power of the critical lattice weight is summable against
the exact scalar coefficient of a smooth periodic datum. -/
theorem summable_latticeModeWeight_pow_scalarCoefficient {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (n : ℕ) :
    Summable (fun k : LatticeMode =>
      latticeModeWeight k ^ n * ‖scalarCoefficient f k‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_scalarCoefficient_productBound_at hf hp (n + 2) (n + 4)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg
      (pow_nonneg (zero_le_one.trans (one_le_latticeModeWeight k)) n) (norm_nonneg _)) _
    (summable_productWeightTail.mul_left C)
  intro k
  let P := (1 + |(k.1 : ℝ)|) * TorusInverse.weight k.2
  have hP : 0 < P := mul_pos (by positivity) (TorusInverse.weight_pos k.2)
  have hw : latticeModeWeight k ^ n ≤ P ^ n :=
    pow_le_pow_left₀ (zero_le_one.trans (one_le_latticeModeWeight k))
      (latticeModeWeight_le_productWeight k) n
  have hden : 0 < (1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4 :=
    mul_pos (pow_pos (by positivity) 2) (pow_pos (TorusInverse.weight_pos k.2) 4)
  have hmain : P ^ n * ‖scalarCoefficient f k‖ ≤
      C / ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) := by
    apply (le_div_iff₀ hden).2
    calc
      (P ^ n * ‖scalarCoefficient f k‖) *
          ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) =
        (1 + |(k.1 : ℝ)|) ^ (n + 2) *
          TorusInverse.weight k.2 ^ (n + 4) *
            ‖scalarCoefficient f k‖ := by
              dsimp [P]
              rw [mul_pow, pow_add, pow_add]
              ring
      _ ≤ C := hbound k
  have htarget : latticeModeWeight k ^ n * ‖scalarCoefficient f k‖ ≤
      C / ((1 + |(k.1 : ℝ)|) ^ 2 * TorusInverse.weight k.2 ^ 4) :=
    (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans hmain
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm] using htarget

/-- All polynomial moments of the exact native vector coefficient are
summable. -/
theorem periodicInitialDatum_all_nativeCoefficient_moments
    {u₀ : VelocityField} (hu₀ : PeriodicInitialDatum u₀) (n : ℕ) :
    Summable (fun k : LatticeMode =>
      latticeModeWeight k ^ n * complexEuclideanNorm (nativeCoefficient u₀ k)) := by
  have hc (i : Fin 3) := summable_latticeModeWeight_pow_scalarCoefficient
    (nativeScalarSource_smooth hu₀.1 i)
    (nativeScalarSource_periodic hu₀.2.2 i) n
  have hsum : Summable (fun k : LatticeMode => ∑ i : Fin 3,
      latticeModeWeight k ^ n * ‖nativeCoefficient u₀ k i‖) := by
    simpa [Fin.sum_univ_succ] using
      (hc (0 : Fin 3)).add ((hc (1 : Fin 3)).add (hc (2 : Fin 3)))
  have hsum' : Summable (fun k : LatticeMode =>
      latticeModeWeight k ^ n * ∑ i : Fin 3, ‖nativeCoefficient u₀ k i‖) := by
    convert hsum using 1
    funext k
    rw [Finset.mul_sum]
  exact hsum'.of_nonneg_of_le
    (fun k => mul_nonneg
      (pow_nonneg (zero_le_one.trans (one_le_latticeModeWeight k)) n) (norm_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left
      (complexEuclideanNorm_le_coordinateSum (nativeCoefficient u₀ k))
      (pow_nonneg (zero_le_one.trans (one_le_latticeModeWeight k)) n))

/-- Every polynomial moment required by the smoothing hierarchy is already
finite for the normalized raw initial carrier. -/
theorem periodicInitialDatum_all_rawCarrier_moments
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) (n : ℕ) :
    LatticePolynomialMoment n (rawInitialCarrier u₀ hu₀) := by
  have hbase := periodicInitialDatum_all_nativeCoefficient_moments hu₀ n
  apply (hbase.mul_left ‖physicalToRawAmplitude‖).congr
  intro k
  unfold polynomialMomentAmplitude rawInitialCarrier complexEuclideanNorm
  rw [congrFun (weightedLatticeCoefficient_smul physicalToRawAmplitude
      (nativeInitialCarrier u₀ hu₀)) k,
    Pi.smul_apply, nativeInitialCarrier_coefficient,
    complexEuclideanPoint_smul, norm_smul]
  simp only [Real.rpow_natCast]
  ring

/-- Exact native-data consumer: every official periodic datum initializes the
constructed physical local evolution with the faithful raw normalization,
reconstruction, divergence, reality, and all polynomial moments. -/
theorem exists_physical_local_evolution_of_periodicInitialDatum
    (ν : ℝ) (hν : 0 < ν) (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ A : ℝ → WeightedLatticeBanach,
      A 0 = rawInitialCarrier u₀ hu₀ ∧
      physicalMildVelocity A 0 = u₀ ∧
      Continuous A ∧
      (∀ s, LatticeDivergenceFree (A s)) ∧
      (∀ s, LatticeAntiHermitian (A s)) ∧
      (∀ s, ‖A s‖ ≤ criticalMildBoundedRadius ‖rawInitialCarrier u₀ hu₀‖) ∧
      (∀ t ∈ Ioo (0 : ℝ) T,
        (Summable fun k : LatticeMode => quarterFrequencyWeight k *
          (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
            complexEuclideanNorm
              (weightedLatticeCoefficient (physicalCarrier (A t)) k))) ∧
        (∀ k i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
          (mildRawTimeDerivative (rawMildViscosity ν) A t k i) t) ∧
        (Summable fun k : LatticeMode => complexEuclideanNorm
          (mildRawTimeDerivative (rawMildViscosity ν) A t k)) ∧
        ∀ k,
          rawToPhysicalAmplitude • mildRawTimeDerivative (rawMildViscosity ν) A t k +
            periodOneConvectionCoefficient k (physicalCarrier (A t)) (physicalCarrier (A t)) +
            periodOneViscousCoefficient ν k
              (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
            periodOneGradientCoefficient k
              (periodOnePressureCoefficient k (physicalCarrier (A t)) (physicalCarrier (A t))) = 0) ∧
      (∀ n : ℕ, LatticePolynomialMoment n (A 0)) := by
  obtain ⟨T, hT, A, hA0, hAc, hdiv, hreal, hbound, hpositive⟩ :=
    exists_physical_local_evolution ν hν (rawInitialCarrier u₀ hu₀)
      (latticeDivergenceFree_rawInitialCarrier u₀ hu₀)
      (latticeAntiHermitian_rawInitialCarrier u₀ hu₀)
  refine ⟨T, hT, A, hA0, ?_, hAc, hdiv, hreal, hbound, hpositive, ?_⟩
  · calc
      physicalMildVelocity A 0 =
          physicalMildVelocity (fun _ => rawInitialCarrier u₀ hu₀) 0 := by
            simp only [physicalMildVelocity,
              reconstructedVelocity_eq_physicalFourierReconstruction]
            rw [hA0]
      _ = u₀ := physicalMildVelocity_rawInitialCarrier_eq u₀ hu₀
  · intro n
    rw [hA0]
    exact periodicInitialDatum_all_rawCarrier_moments u₀ hu₀ n

end Navier.Analysis.PeriodicInitialPhysicalEvolution
