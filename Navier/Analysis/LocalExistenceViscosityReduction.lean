import Navier.Analysis.RestartBKMConsumer
import Navier.Analysis.ViscosityAdmissibility

/-!
# Normalize the local-existence leaf to viscosity one

The BKM/restart consumer currently retains `LocalClassicalExistence`, whose
outer quantifier ranges over every positive viscosity.  The repository already
transports the full global solution contract across viscosity, but its local
`SolvesBefore` carrier had no corresponding bridge.

This module supplies that bridge.  Scaling

`uₐ(t,x) = a u(a t,x)`, `pₐ(t,x) = a² p(a t,x)`

maps a solution before `T` at viscosity `μ` to a solution before `T/a` at
viscosity `a μ`.  Smoothness, the pointwise equation, finite slice energy, and
the initial-energy inequality are all transported.  Consequently the full
local-existence leaf is equivalent to its viscosity-one surface.  The final
theorem consumes that normalized leaf in the checked BKM/restart crown
endpoint; the uniform BKM and restart inputs remain explicit.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.LocalExistenceViscosityReduction

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste
open Navier.Analysis.RestartBKMConsumer
open Navier.Analysis.ViscosityTransport
open Navier.Analysis.ViscosityAdmissibility

/-- The time-dilation map sends the scaled half-open horizon into the original
half-open horizon. -/
theorem mapsTo_spacetimeBefore_viscosityTimeMap
    (a T : ℝ) (ha : 0 < a) :
    MapsTo (viscosityTimeMap a) (spacetimeBefore (T / a))
      (spacetimeBefore T) := by
  intro z hz
  refine ⟨⟨mul_nonneg ha.le hz.1.1, ?_⟩, hz.2⟩
  have h := (lt_div_iff₀ ha).mp hz.1.2
  change a * z.1 < T
  simpa only [mul_comm] using h

/-- Joint velocity smoothness transports to the divided horizon. -/
theorem smoothVelocityBefore_viscosityScaled
    (a T : ℝ) (ha : 0 < a) (u : VelocityEvolution)
    (hu : SmoothVelocityBefore T u) :
    SmoothVelocityBefore (T / a) (viscosityScaledVelocity a u) := by
  have hcomp := hu.comp (contDiff_viscosityTimeMap a).contDiffOn
    (mapsTo_spacetimeBefore_viscosityTimeMap a T ha)
  have hscaled := hcomp.const_smul a
  simpa only [SmoothVelocityBefore, viscosityScaledVelocity,
    viscosityTimeMap, Function.comp_apply] using hscaled

/-- Joint pressure smoothness transports to the divided horizon. -/
theorem smoothPressureBefore_viscosityScaled
    (a T : ℝ) (ha : 0 < a) (p : PressureEvolution)
    (hp : SmoothPressureBefore T p) :
    SmoothPressureBefore (T / a) (viscosityScaledPressure a p) := by
  have hcomp := hp.comp (contDiff_viscosityTimeMap a).contDiffOn
    (mapsTo_spacetimeBefore_viscosityTimeMap a T ha)
  have hscaled := hcomp.const_smul (a ^ 2)
  simpa only [SmoothPressureBefore, viscosityScaledPressure,
    viscosityTimeMap, Function.comp_apply, smul_eq_mul] using hscaled

/-- The pointwise PDE on a half-open horizon transports with viscosity weight
one and horizon weight minus one. -/
theorem satisfiesNavierStokesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hEquation : SatisfiesNavierStokesBefore mu f T u p) :
    SatisfiesNavierStokesBefore (a * mu) (viscosityScaledForce a f)
      (T / a) (viscosityScaledVelocity a u)
      (viscosityScaledPressure a p) := by
  intro t ht htT x
  have hScaledTime : 0 ≤ a * t := mul_nonneg ha.le ht
  have hScaledBefore : a * t < T := by
    have h := (lt_div_iff₀ ha).mp htT
    simpa only [mul_comm] using h
  have hAtScaledPoint := hEquation (a * t) hScaledTime hScaledBefore x
  rw [timeDerivative_viscosityScaled a ha u t ht x]
  rw [convection_viscosityScaled, laplacian_viscosityScaled,
    pressureGradient_viscosityScaled]
  change
    a ^ 2 • timeDerivative u (a * t) x +
        a ^ 2 • convection u (a * t) x =
      (a * mu) • (a • laplacian u (a * t) x) -
          a ^ 2 • pressureGradient p (a * t) x +
        a ^ 2 • f (a * t) x
  rw [← smul_add, hAtScaledPoint]
  simp only [smul_add, smul_sub, smul_smul]
  congr 1
  ring_nf

/-- The four local classical PDE clauses transport to the divided horizon. -/
theorem originalSolvesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution)
    (h : OriginalSolvesBefore mu T u p) :
    OriginalSolvesBefore (a * mu) (T / a)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p) := by
  rcases h with ⟨hu, hp, hinc, heq⟩
  refine ⟨smoothVelocityBefore_viscosityScaled a T ha u hu,
    smoothPressureBefore_viscosityScaled a T ha p hp, ?_, ?_⟩
  · intro t ht htT x
    have hScaledBefore : a * t < T := by
      have h' := (lt_div_iff₀ ha).mp htT
      simpa only [mul_comm] using h'
    rw [divergence_viscosityScaled,
      hinc (a * t) (mul_nonneg ha.le ht) hScaledBefore x, mul_zero]
  · simpa only [viscosityScaledForce_zero] using
      satisfiesNavierStokesBefore_viscosityScaled_mul
        a ha mu T zeroForce u p heq

/-- The full admissible local solution class transports across viscosity.
The energy inequality is unchanged after multiplying both sides by `a²`. -/
theorem solvesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution)
    (h : SolvesBefore mu T u p) :
    SolvesBefore (a * mu) (T / a)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p) where
  classical := originalSolvesBefore_viscosityScaled_mul a ha mu T u p h.classical
  finite_energy := by
    intro t ht htT
    apply finiteEnergy_viscosityScaled a ha u t
    apply h.finite_energy (a * t) (mul_nonneg ha.le ht)
    have h' := (lt_div_iff₀ ha).mp htT
    simpa only [mul_comm] using h'
  energy_le_initial := by
    intro t ht htT
    rw [kineticEnergy_viscosityScaled a ha,
      kineticEnergy_viscosityScaled a ha]
    simp only [mul_zero]
    apply mul_le_mul_of_nonneg_left
    · apply h.energy_le_initial (a * t) (mul_nonneg ha.le ht)
      have h' := (lt_div_iff₀ ha).mp htT
      simpa only [mul_comm] using h'
    · positivity

/-- The exact unit-viscosity surface of the local-existence leaf. -/
def LocalClassicalExistenceAtViscosityOne : Prop :=
  ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore 1 T u p

/-- Local classical existence for all positive viscosities is equivalent to
its unit-viscosity surface.  The reverse implication applies unit-viscosity
existence to the inverse-amplitude datum and scales the resulting local
solution forward. -/
theorem localClassicalExistence_iff_atViscosityOne :
    LocalClassicalExistence ↔ LocalClassicalExistenceAtViscosityOne := by
  constructor
  · intro h u₀ hu₀
    exact h 1 zero_lt_one u₀ hu₀
  · intro h nu hnu u₀ hu₀
    let base := viscosityScaledSchwartzDatum nu⁻¹ u₀
    have hbase : DivergenceFreeInitial base :=
      divergenceFreeInitial_viscosityScaledSchwartzDatum nu⁻¹ u₀ hu₀
    rcases h base hbase with ⟨T, hT, u, p, hinit, hsol⟩
    refine ⟨T / nu, div_pos hT hnu,
      viscosityScaledVelocity nu u, viscosityScaledPressure nu p, ?_, ?_⟩
    · intro x
      have hscaled := initialCondition_viscosityScaledSchwartz nu base u hinit x
      simpa only [base, viscosityScaledSchwartzDatum, smul_smul,
        mul_inv_cancel₀ hnu.ne', one_smul] using hscaled
    · simpa only [mul_one] using
        solvesBefore_viscosityScaled_mul nu hnu 1 T u p hsol

/-- The viscosity-normalized local leaf is consumed directly by the checked
BKM/restart whole-space endpoint.  Only the viscosity parameter has been
discharged; the unit-viscosity local theorem, uniform BKM estimate, and restart
engine remain explicit. -/
theorem wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
    (hlocal : LocalClassicalExistenceAtViscosityOne)
    (hbkm : NSBKMUniformVorticityApriori)
    (hrestart : HorizonIndependentRestart bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  exact wholeSpaceGlobalRegularity_of_local_bkmRestart
    (localClassicalExistence_iff_atViscosityOne.mpr hlocal) hbkm hrestart

end Navier.Analysis.LocalExistenceViscosityReduction

set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.localClassicalExistence_iff_atViscosityOne
set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.localClassicalExistence_iff_atViscosityOne
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
