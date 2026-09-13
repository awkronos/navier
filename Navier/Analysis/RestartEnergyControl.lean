import Navier.Analysis.RestartPaste

/-!
# Horizon-independent preterminal energy control

`SolvesBefore` already carries the dissipative energy inequality
`kineticEnergy u t ≤ kineticEnergy u 0` on every time strictly before its
horizon.  This module packages exactly that invariant in the extended-real
critical-quantity interface used by the original whole-space A consumer.

The supremum is taken over `Ico 0 T`, rather than at `T`, because the
half-open solution predicate deliberately constrains no terminal value.  The
resulting quantity has a horizon-independent bound determined solely by the
Schwartz datum.  Consequently the original three-premise consumer needs only
local existence and a horizon-independent restart for this concrete energy
quantity; its a priori-control premise is discharged here.

This does not assert that energy controls a three-dimensional restart.  That
remaining dynamical statement is exactly
`HorizonIndependentRestart preterminalEnergyControl`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Navier.Analysis.RestartEnergyControl

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.RestartPaste

/-- Euclidean kinetic energy of a Schwartz initial datum, expressed through
the constant-in-time evolution used by `kineticEnergy`. -/
def initialKineticEnergy (u₀ : SchwartzVelocity) : ℝ :=
  kineticEnergy (fun _ x => u₀ x) 0

/-- The supremum of the actual Euclidean kinetic energy over all constrained
times strictly before the solution horizon. -/
def preterminalEnergyControl : CriticalQuantity :=
  fun T u => ⨆ t ∈ Ico (0 : ℝ) T, ENNReal.ofReal (kineticEnergy u t)

/-- The preterminal supremum sees the initial slice on every positive
horizon.  In particular the control is not the degenerate zero quantity when
the initial energy is positive. -/
theorem ofReal_kineticEnergy_zero_le_preterminalEnergyControl
    (u : VelocityEvolution) {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal (kineticEnergy u 0) ≤ preterminalEnergyControl T u := by
  exact le_iSup₂_of_le (0 : ℝ) ⟨le_rfl, hT⟩ le_rfl

theorem preterminalEnergyControl_pos_of_initialEnergy_pos
    (u : VelocityEvolution) {T : ℝ} (hT : 0 < T)
    (henergy : 0 < kineticEnergy u 0) :
    0 < preterminalEnergyControl T u := by
  exact (ENNReal.ofReal_pos.mpr henergy).trans_le
    (ofReal_kineticEnergy_zero_le_preterminalEnergyControl u hT)

@[simp] theorem preterminalEnergyControl_zero (T : ℝ) :
    preterminalEnergyControl T (fun _ _ => 0) = 0 := by
  simp [preterminalEnergyControl, Navier.kineticEnergy]

theorem initialKineticEnergy_nonneg (u₀ : SchwartzVelocity) :
    0 ≤ initialKineticEnergy u₀ := by
  simpa [initialKineticEnergy, Navier.kineticEnergy] using
    (integral_nonneg
      (fun x : Space => Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) => sq_nonneg (u₀ x i))))

/-- Every admissible finite-horizon solution lies in the datum-determined
energy sublevel set, uniformly in the horizon. -/
theorem preterminalEnergyControl_le_initial
    {nu T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    {u₀ : SchwartzVelocity}
    (hinit : ∀ x : Space, u 0 x = u₀ x)
    (hsol : SolvesBefore nu T u p) :
    preterminalEnergyControl T u ≤ ENNReal.ofReal (initialKineticEnergy u₀) := by
  unfold preterminalEnergyControl
  exact iSup₂_le (fun t ht => ENNReal.ofReal_le_ofReal
    ((hsol.energy_le_initial t ht.1 ht.2).trans_eq (by
      unfold initialKineticEnergy Navier.kineticEnergy
      rw [show u 0 = (fun x => u₀ x) from funext hinit])))

/-- The energy inequality supplies the a priori leaf of the original
whole-space continuation consumer with a bound independent of `T`. -/
theorem aPrioriCriticalControl_preterminalEnergy :
    APrioriCriticalControl preterminalEnergyControl := by
  intro nu _hnu u₀ _hdiv
  let M : ℝ≥0 := ⟨initialKineticEnergy u₀, initialKineticEnergy_nonneg u₀⟩
  refine ⟨M, ?_⟩
  intro T _hT u p hinit hsol
  exact (preterminalEnergyControl_le_initial hinit hsol).trans_eq
    (ENNReal.ofReal_eq_coe_nnreal (initialKineticEnergy_nonneg u₀))

/-- The original whole-space regularity consumer with its energy-control
premise discharged.  The two remaining inputs are the genuine local
existence and dynamical restart obligations. -/
theorem wholeSpaceGlobalRegularity_of_local_horizonIndependentEnergyRestart
    (hlocal : LocalClassicalExistence)
    (hrestart : HorizonIndependentRestart preterminalEnergyControl) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  exact wholeSpaceGlobalRegularity_of_local_continuation_apriori
    preterminalEnergyControl hlocal
    (normalizedContinuation_of_horizonIndependentRestart hrestart)
    aPrioriCriticalControl_preterminalEnergy

end Navier.Analysis.RestartEnergyControl

#check Navier.Analysis.RestartEnergyControl.preterminalEnergyControl_le_initial
#check Navier.Analysis.RestartEnergyControl.aPrioriCriticalControl_preterminalEnergy
#check Navier.Analysis.RestartEnergyControl.wholeSpaceGlobalRegularity_of_local_horizonIndependentEnergyRestart
#check Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori

#print axioms Navier.Analysis.RestartEnergyControl.initialKineticEnergy_nonneg
#print axioms Navier.Analysis.RestartEnergyControl.ofReal_kineticEnergy_zero_le_preterminalEnergyControl
#print axioms Navier.Analysis.RestartEnergyControl.preterminalEnergyControl_pos_of_initialEnergy_pos
#print axioms Navier.Analysis.RestartEnergyControl.preterminalEnergyControl_zero
#print axioms Navier.Analysis.RestartEnergyControl.preterminalEnergyControl_le_initial
#print axioms Navier.Analysis.RestartEnergyControl.aPrioriCriticalControl_preterminalEnergy
#print axioms Navier.Analysis.RestartEnergyControl.wholeSpaceGlobalRegularity_of_local_horizonIndependentEnergyRestart
#print axioms Navier.Analysis.RestartPaste.normalizedContinuation_of_horizonIndependentRestart
#print axioms Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori
