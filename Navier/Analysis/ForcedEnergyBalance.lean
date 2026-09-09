import Navier.Analysis.EnergyPointwiseBalance
import Navier.Breakdown.MaximalNonextension

/-!
# Forced local energy balance before breakdown

Retain the force-work term in the existing energy decomposition, and consume
the actual partial-solution predicate. This applies before a possible singular
time and never assumes a global solution. It is the local continuum identity
behind the solver's force-injection and viscous-dissipation diagnostics.
Spatial integration and differentiation under an integral need additional
integrability and boundary estimates; they are not asserted here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff

namespace Navier.Analysis.ForcedEnergyBalance

open EnergyViscousDissipation EnergyPointwiseBalance Breakdown

/-- The local energy identity needs only the PDE and incompressibility at
the point under consideration, rather than a global existence premise. -/
theorem forced_pointwise_energy_balance
    (ν : ℝ) (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (htime : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t)
    (hspace : DifferentiableAt ℝ (u t) x)
    (hsecond : ∀ j : Fin 3, DifferentiableAt ℝ (coordinateDerivativeField (u t) j) x)
    (hpressure : DifferentiableAt ℝ (p t) x)
    (hdiv : staticDivergence (u t) x = 0)
    (heq : timeDerivative u t x + convection u t x =
      ν • laplacian u t x - pressureGradient p t x + f t x) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x) (Set.Ici 0) t 1 +
      ν * derivativeEnergyDensity (u t) x =
      ν * staticDivergence (viscousEnergyFlux (u t)) x -
      staticDivergence (fun y => p t y • u t y) x -
      staticDivergence (kineticEnergyFlux (u t)) x +
      ∑ i : Fin 3, f t x i * u t x i := by
  have hp : (∑ i : Fin 3, pressureGradient p t x i * u t x i) =
      staticDivergence (fun y => p t y • u t y) x := by
    rw [staticDivergence_smul (p t) (u t) x hpressure hspace, hdiv]
    simp only [mul_zero, add_zero]
    rfl
  rw [kineticEnergyDensity_timeDerivative u t ht x htime,
    eq_sub_of_add_eq heq]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  rw [laplacian_work_eq_divergence_sub_derivativeEnergy u t x hspace hsecond,
    hp, convection_work_eq_staticDivergence u t x hspace hdiv]
  ring

/-- Every genuine partial classical solution supplies the analytic premises
of the forced energy law at interior times, including second spatial derivatives. -/
theorem forced_pointwise_energy_balance_of_partialSolution
    {ν T : ℝ} {f : ForceField} {u₀ : VelocityField}
    (sol : PartialClassicalSolution ν f u₀ T)
    (t : ℝ) (ht : 0 < t) (htT : t < T) (x : Space) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (sol.velocity s) x)
        (Set.Ici 0) t 1 + ν * derivativeEnergyDensity (sol.velocity t) x =
      ν * staticDivergence (viscousEnergyFlux (sol.velocity t)) x -
      staticDivergence (fun y => sol.pressure t y • sol.velocity t y) x -
      staticDivergence (kineticEnergyFlux (sol.velocity t)) x +
      ∑ i : Fin 3, f t x i * sol.velocity t x i := by
  have hn : spacetimeBefore T ∈ nhds (t, x) := by
    apply Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨ht, htT⟩, Set.mem_univ x⟩)
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩
  have hu : ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.velocity z.1 z.2) (t, x) :=
    sol.velocity_smooth.contDiffAt hn
  have hp : ContDiffAt ℝ ∞ (fun z : ℝ × Space => sol.pressure z.1 z.2) (t, x) :=
    sol.pressure_smooth.contDiffAt hn
  have hs : ContDiff ℝ ∞ (sol.velocity t) := by
    have hparam : ContDiff ℝ ∞ (fun y : Space => (t, y)) := by fun_prop
    exact sol.velocity_smooth.comp_contDiff hparam
      (fun y => ⟨⟨ht.le, htT⟩, Set.mem_univ y⟩)
  apply forced_pointwise_energy_balance ν f sol.velocity sol.pressure t ht.le x
  · have hparam : DifferentiableAt ℝ (fun s : ℝ => (s, x)) t := by fun_prop
    exact ((hu.differentiableAt (by simp)).comp t hparam).differentiableWithinAt
  · exact hs.differentiable (by simp) x
  · exact fun j => differentiable_coordinateDerivativeField_of_contDiff _ hs j x
  · exact (hp.differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  · exact sol.incompressible t ht.le htT x
  · exact sol.equation t ht.le htT x

end Navier.Analysis.ForcedEnergyBalance

#print axioms Navier.Analysis.ForcedEnergyBalance.forced_pointwise_energy_balance
#print axioms Navier.Analysis.ForcedEnergyBalance.forced_pointwise_energy_balance_of_partialSolution
