import Navier.Analysis.EnergyConvectionCancellation

/-!
# Pointwise kinetic-energy time derivative

This file differentiates the coordinate kinetic-energy density along a
velocity evolution using the same right-within derivative on `Set.Ici 0` as
the project momentum equation.  It then rewrites the time-derivative work by
the pointwise Navier--Stokes equation.

Everything here is local in time and space.  No time or spatial integral,
boundary passage, or energy identity is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff

namespace Navier

/-- Smooth spacetime velocity gives the exact right-within differentiability
of every fixed-space time curve used by `timeDerivative`. -/
theorem differentiableWithinAt_timeSlice_of_smoothVelocity
    (u : VelocityEvolution) (hu : SmoothVelocityOnNonnegativeTime u)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t := by
  have hparam : ContDiffOn ℝ ∞ (fun s : ℝ => (s, x)) (Set.Ici 0) := by
    fun_prop
  have hcurve : ContDiffOn ℝ ∞ (fun s : ℝ => u s x) (Set.Ici 0) := by
    change ContDiffOn ℝ ∞
      ((fun z : ℝ × Space => u z.1 z.2) ∘ fun s : ℝ => (s, x))
      (Set.Ici 0)
    exact hu.comp hparam (by
      intro s hs
      exact ⟨hs, Set.mem_univ x⟩)
  exact hcurve.differentiableOn (by simp) t ht

/-- Kinetic-energy density along a fixed-space time curve is differentiable
whenever the velocity time curve is differentiable within `Set.Ici 0`. -/
theorem differentiableWithinAt_kineticEnergyDensity_time
    (u : VelocityEvolution) (t : ℝ) (x : Space)
    (hu : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => kineticEnergyDensity (u s) x) (Set.Ici 0) t := by
  unfold kineticEnergyDensity
  apply DifferentiableWithinAt.const_mul
  exact DifferentiableWithinAt.fun_sum fun i _ =>
    ((differentiableWithinAt_pi.1 hu i).mul
      (differentiableWithinAt_pi.1 hu i))

/-- Exact right-within derivative of coordinate kinetic-energy density. -/
theorem fderivWithin_kineticEnergyDensity_time
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (hu : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ∑ i, (fderivWithin ℝ (fun s : ℝ => u s x) (Set.Ici 0) t 1) i *
        u t x i := by
  have huniq : UniqueDiffWithinAt ℝ (Set.Ici 0) t :=
    uniqueDiffOn_Ici 0 t ht
  have hcoord : ∀ i : Fin 3,
      DifferentiableWithinAt ℝ (fun s : ℝ => u s x i) (Set.Ici 0) t :=
    fun i => differentiableWithinAt_pi.1 hu i
  have hsum : DifferentiableWithinAt ℝ
      (fun s : ℝ => ∑ i, u s x i * u s x i) (Set.Ici 0) t :=
    DifferentiableWithinAt.fun_sum fun i _ => (hcoord i).mul (hcoord i)
  have hsum_fderiv :
      fderivWithin ℝ (fun s : ℝ => ∑ i, u s x i * u s x i)
          (Set.Ici 0) t =
        ∑ i, fderivWithin ℝ (fun s : ℝ => u s x i * u s x i)
          (Set.Ici 0) t := by
    rw [fderivWithin_fun_sum huniq]
    intro i _
    exact (hcoord i).mul (hcoord i)
  change fderivWithin ℝ
      (fun s : ℝ => (1 / 2 : ℝ) * ∑ i, u s x i * u s x i)
      (Set.Ici 0) t 1 =
    ∑ i, (fderivWithin ℝ (fun s : ℝ => u s x) (Set.Ici 0) t 1) i *
      u t x i
  rw [fderivWithin_const_mul huniq hsum (1 / 2 : ℝ)]
  simp only [smul_apply, smul_eq_mul]
  rw [hsum_fderiv]
  simp only [sum_apply,
    fderivWithin_fun_mul huniq (hcoord _) (hcoord _),
    add_apply, smul_apply,
    fderivWithin_apply hu huniq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_add_distrib]
  ring_nf

/-- The derivative formula expressed with the project's `timeDerivative`
convention. -/
theorem kineticEnergyDensity_timeDerivative
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (hu : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ∑ i, timeDerivative u t x i * u t x i := by
  simpa only [timeDerivative] using
    fderivWithin_kineticEnergyDensity_time u t ht x hu

/-- A smooth project velocity satisfies the kinetic-energy time-derivative
formula at every nonnegative time. -/
theorem kineticEnergyDensity_timeDerivative_of_smoothVelocity
    (u : VelocityEvolution) (hu : SmoothVelocityOnNonnegativeTime u)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ∑ i, timeDerivative u t x i * u t x i :=
  kineticEnergyDensity_timeDerivative u t ht x
    (differentiableWithinAt_timeSlice_of_smoothVelocity u hu t ht x)

/-- Rewriting the momentum equation separates pointwise viscosity, pressure,
force, and convection work. -/
theorem kineticEnergyDensity_timeDerivative_eq_work
    (ν : ℝ) (f : ForceField) (u : VelocityEvolution)
    (p : PressureEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (hu : DifferentiableWithinAt ℝ (fun s : ℝ => u s x) (Set.Ici 0) t)
    (hEquation : SatisfiesNavierStokes ν f u p) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ν * (∑ i, laplacian u t x i * u t x i) -
      (∑ i, pressureGradient p t x i * u t x i) +
      (∑ i, f t x i * u t x i) -
      (∑ i, convection u t x i * u t x i) := by
  rw [kineticEnergyDensity_timeDerivative u t ht x hu]
  have htime :
      timeDerivative u t x =
        ν • laplacian u t x - pressureGradient p t x + f t x -
          convection u t x :=
    eq_sub_of_add_eq (hEquation t ht x)
  rw [htime]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, Finset.mul_sum]

/-- The work decomposition specialized to a complete project classical
solution. -/
theorem kineticEnergyDensity_timeDerivative_eq_work_of_classicalSolution
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsClassicalSolution ν f u₀ u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ν * (∑ i, laplacian u t x i * u t x i) -
      (∑ i, pressureGradient p t x i * u t x i) +
      (∑ i, f t x i * u t x i) -
      (∑ i, convection u t x i * u t x i) :=
  kineticEnergyDensity_timeDerivative_eq_work ν f u p t ht x
    (differentiableWithinAt_timeSlice_of_smoothVelocity
      u h.velocity_smooth t ht x)
    h.equation

end Navier
