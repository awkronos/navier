import Navier.Analysis.CriticalMildTrajectoryReality
import Navier.Analysis.CriticalMildSmoothBootstrap

/-!
# A constructed physical local trajectory with evolving regularity

The same fixed point carries reality, the actual mild equation, and the first
joint time-space estimates. No evolving trajectory or regularity premise is
supplied by the caller. The explicit positive horizon depends on the initial
critical norm; this is local existence, not a horizon-uniform estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PhysicalLocalEvolution

open Set Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.CriticalMildHigherMomentBootstrap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildSmoothBootstrap
open Navier.Analysis.CriticalMildTrajectoryReality
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.OfficialABEncoding

theorem exists_physical_local_evolution
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a) (hareal : LatticeAntiHermitian a) :
    ∃ T : ℝ, 0 < T ∧ ∃ A : ℝ → WeightedLatticeBanach,
      A 0 = a ∧ Continuous A ∧ (∀ s, LatticeDivergenceFree (A s)) ∧
      (∀ s, LatticeAntiHermitian (A s)) ∧
      (∀ s, ‖A s‖ ≤ criticalMildBoundedRadius ‖a‖) ∧
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
              (periodOnePressureCoefficient k (physicalCarrier (A t)) (physicalCarrier (A t))) = 0) := by
  let μ := rawMildViscosity ν
  have hμ : 0 < μ := by dsimp [μ, rawMildViscosity]; positivity
  let R := criticalMildBoundedRadius ‖a‖
  let T := criticalMildBoundedHorizon μ ‖a‖
  have hR : 1 ≤ R := by
    dsimp [R, criticalMildBoundedRadius]
    linarith [norm_nonneg a]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRa : ‖a‖ + 1 ≤ R := le_rfl
  have hμsqrt : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hq : 0 < Real.sqrt μ / (8 * R ^ 2) := by positivity
  have hsqrt : Real.sqrt T = Real.sqrt μ / (8 * R ^ 2) := by
    dsimp [T, criticalMildBoundedHorizon]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hT : 0 < T := sq_pos_of_pos hq
  have hbudget : ‖a‖ + (2 * Real.sqrt T / Real.sqrt μ) * R ^ 2 ≤ R := by
    rw [hsqrt]
    have hs : Real.sqrt μ ≠ 0 := ne_of_gt hμsqrt
    field_simp
    nlinarith [sq_nonneg R, hRa]
  have hcontr : (4 * Real.sqrt T / Real.sqrt μ) * R < 1 := by
    rw [hsqrt]
    have hs : Real.sqrt μ ≠ 0 := ne_of_gt hμsqrt
    field_simp
    nlinarith [hR]
  obtain ⟨u, hreal, _, _, hmild⟩ :=
    exists_criticalMild_trajectory_antiHermitian μ hμ a hareal hT.le hRpos.le hbudget hcontr
  let A := criticalMildPathExtension T hT.le u.1
  have hAc : Continuous A := continuous_criticalMildPathExtension T hT.le u.1
  have hdiv : ∀ s, LatticeDivergenceFree (A s) :=
    criticalMildPathBallExtension_divergenceFree hT.le u
  have hbound : ∀ s, ‖A s‖ ≤ R := criticalMildPathBallExtension_norm_le hT.le u
  have hrealA : ∀ s, LatticeAntiHermitian (A s) := by
    intro s
    exact hreal (projIcc (0 : ℝ) T hT.le s)
  have heq : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1 := by
    intro s hs
    have h := hmild ⟨s, hs⟩
    simpa only [A, criticalMildPathExtension_apply T hT.le u.1 hs] using h
  have hzero : A 0 = a := by
    have h := heq 0 ⟨le_rfl, hT.le⟩
    rw [criticalMildImage_zero_nonlinear,
      Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_zero_of_divergenceFree
        μ hμ.le a ha] at h
    exact h
  refine ⟨T, hT, A, hzero, hAc, hdiv, hrealA, hbound, ?_⟩
  intro t ht
  have h := mildFixedPoint_firstJointBootstrap_at
    ν hν a ha A hAc hdiv hRpos.le ht (fun s _ => hbound s) heq
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

end Navier.Analysis.PhysicalLocalEvolution

#print axioms Navier.Analysis.PhysicalLocalEvolution.exists_physical_local_evolution
