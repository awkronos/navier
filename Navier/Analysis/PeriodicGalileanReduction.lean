import Navier.Analysis.ViscosityForceDecay

/-!
# Moving-frame covariance on the native periodic carrier

The transformation `v(t,x) = u(t,x+t c)-c` removes a constant velocity
without changing viscosity or introducing forcing.  The right-within time
derivative at zero is retained: all chain rules are on the actual closed
nonnegative-time domain.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace Navier.Analysis.PeriodicGalileanReduction

open Navier Set

def movingVelocity (c : Space) (u : VelocityEvolution) : VelocityEvolution :=
  fun t x => u t (x + t • c) - c

def movingPressure (c : Space) (p : PressureEvolution) : PressureEvolution :=
  fun t x => p t (x + t • c)

def movingDatum (c : Space) (u₀ : VelocityField) : VelocityField :=
  fun x => u₀ x - c

def movingSpacetime (c : Space) : ℝ × Space → ℝ × Space :=
  fun z => (z.1, z.2 + z.1 • c)

theorem contDiff_movingSpacetime (c : Space) :
    ContDiff ℝ ∞ (movingSpacetime c) :=
  contDiff_fst.prodMk (contDiff_snd.add (contDiff_fst.smul_const c))

theorem movingSpacetime_mapsTo (c : Space) :
    MapsTo (movingSpacetime c) nonnegativeSpacetime nonnegativeSpacetime := by
  intro z hz
  exact ⟨hz.1, mem_univ _⟩

theorem smoothVelocity_moving (c : Space) {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) :
    SmoothVelocityOnNonnegativeTime (movingVelocity c u) := by
  exact (hu.comp (contDiff_movingSpacetime c).contDiffOn
    (movingSpacetime_mapsTo c)).sub contDiffOn_const

theorem smoothPressure_moving (c : Space) {p : PressureEvolution}
    (hp : SmoothPressureOnNonnegativeTime p) :
    SmoothPressureOnNonnegativeTime (movingPressure c p) := by
  exact hp.comp (contDiff_movingSpacetime c).contDiffOn
    (movingSpacetime_mapsTo c)

theorem spatialDerivative_moving (c : Space) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    spatialDerivative (movingVelocity c u) t x =
      spatialDerivative u t (x + t • c) := by
  unfold spatialDerivative movingVelocity
  rw [fderiv_sub_const, fderiv_comp_add_right]

theorem laplacian_moving (c : Space) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    laplacian (movingVelocity c u) t x = laplacian u t (x + t • c) := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hfirst : (fun y => fderiv ℝ (movingVelocity c u t) y (basisVector i)) =
      (fun y => fderiv ℝ (u t) (y + t • c) (basisVector i)) := by
    funext y
    exact congrArg (fun L : Space →L[ℝ] Space => L (basisVector i))
      (spatialDerivative_moving c u t y)
  rw [hfirst]
  exact congrArg (fun L : Space →L[ℝ] Space => L (basisVector i))
    (fderiv_comp_add_right (𝕜 := ℝ)
      (f := fun y => fderiv ℝ (u t) y (basisVector i)) (x := x) (t • c))

theorem pressureGradient_moving (c : Space) (p : PressureEvolution)
    (t : ℝ) (x : Space) :
    pressureGradient (movingPressure c p) t x =
      pressureGradient p t (x + t • c) := by
  funext i
  change fderiv ℝ (fun y => p t (y + t • c)) x (basisVector i) = _
  rw [fderiv_comp_add_right]
  rfl

private theorem jointDerivative_time {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeDerivative u t x =
      fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2)
        nonnegativeSpacetime (t,x) (1,0) := by
  have hd := (hu.differentiableOn (by simp) (t,x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hc := (hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const x t)
  have h := hd.comp t hc.hasFDerivWithinAt
    (show MapsTo (fun s : ℝ => (s,x)) (Ici 0) nonnegativeSpacetime from
      fun s hs => ⟨hs, mem_univ _⟩)
  have he := h.fderivWithin ((uniqueDiffOn_Ici 0) t ht)
  simpa [timeDerivative, ContinuousLinearMap.comp_apply,
    Function.comp_def, nonnegativeSpacetime] using
    congrArg (fun L : ℝ →L[ℝ] Space => L 1) he

private theorem jointDerivative_space {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) (t : ℝ) (ht : 0 ≤ t)
    (x c : Space) :
    spatialDerivative u t x c =
      fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2)
        nonnegativeSpacetime (t,x) (0,c) := by
  have hd := (hu.differentiableOn (by simp) (t,x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hc := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have h := hd.comp x hc.hasFDerivWithinAt
    (show MapsTo (fun y : Space => (t,y)) univ nonnegativeSpacetime from
      fun y _ => ⟨ht, mem_univ _⟩)
  have he := h.fderivWithin (uniqueDiffWithinAt_univ)
  simpa [spatialDerivative, ContinuousLinearMap.comp_apply,
    Function.comp_def, nonnegativeSpacetime] using
    congrArg (fun L : Space →L[ℝ] Space => L c) he

theorem timeDerivative_moving (c : Space) {u : VelocityEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeDerivative (movingVelocity c u) t x =
      timeDerivative u t (x + t • c) + spatialDerivative u t (x + t • c) c := by
  have hd := (hu.differentiableOn (by simp)
    (t,x+t • c) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hc := (hasFDerivAt_id (𝕜 := ℝ) t).prodMk
    ((hasFDerivAt_const x t).add ((hasFDerivAt_id t).smul_const c))
  have h := (hd.comp t hc.hasFDerivWithinAt
    (show MapsTo (fun s : ℝ => (s,x+s • c)) (Ici 0) nonnegativeSpacetime from
      fun s hs => ⟨hs, mem_univ _⟩)).sub_const c
  have he := h.fderivWithin ((uniqueDiffOn_Ici 0) t ht)
  rw [jointDerivative_time hu t ht, jointDerivative_space hu t ht]
  have hvalue : timeDerivative (movingVelocity c u) t x =
      fderivWithin ℝ (fun z : ℝ × Space => u z.1 z.2)
        nonnegativeSpacetime (t,x+t • c) (1,c) := by
    simpa [timeDerivative, movingVelocity, ContinuousLinearMap.comp_apply,
      Function.comp_def, nonnegativeSpacetime] using
      congrArg (fun L : ℝ →L[ℝ] Space => L 1) he
  rw [hvalue, show ((1 : ℝ),c) = (1,0) + (0,c) by simp, map_add]

theorem divergence_moving (c : Space) (u : VelocityEvolution) (t : ℝ) (x : Space) :
    divergence (movingVelocity c u) t x = divergence u t (x + t • c) := by
  simp only [divergence, spatialDerivative_moving]

theorem convection_moving (c : Space) (u : VelocityEvolution) (t : ℝ) (x : Space) :
    convection (movingVelocity c u) t x =
      convection u t (x + t • c) - spatialDerivative u t (x + t • c) c := by
  rw [convection, spatialDerivative_moving]
  exact map_sub _ _ _

/-- The transport term contributed by the moving coordinates cancels exactly
against the constant velocity removed from nonlinear convection. -/
theorem satisfiesNavierStokes_moving (c : Space) {ν : ℝ}
    {u : VelocityEvolution} {p : PressureEvolution}
    (hu : SmoothVelocityOnNonnegativeTime u)
    (heq : SatisfiesNavierStokes ν zeroForce u p) :
    SatisfiesNavierStokes ν zeroForce (movingVelocity c u) (movingPressure c p) := by
  intro t ht x
  rw [timeDerivative_moving c hu t ht, convection_moving,
    laplacian_moving, pressureGradient_moving]
  calc
    _ = timeDerivative u t (x + t • c) + convection u t (x + t • c) := by abel
    _ = _ := heq t ht (x + t • c)

/-- A complete native periodic classical solution transports to a moving
frame, including the one-sided initial-time equation and periodic pressure. -/
theorem isPeriodicClassicalSolution_moving (c : Space) {ν : ℝ}
    {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν zeroForce u₀ u p) :
    IsPeriodicClassicalSolution ν zeroForce (movingDatum c u₀)
      (movingVelocity c u) (movingPressure c p) := by
  refine ⟨smoothVelocity_moving c h.velocity_smooth,
    smoothPressure_moving c h.pressure_smooth, ?_, ?_,
    satisfiesNavierStokes_moving c h.velocity_smooth h.equation, ?_, ?_⟩
  · intro x
    simp only [movingVelocity, movingDatum, zero_smul, add_zero, h.initial_condition]
  · intro t ht x
    rw [divergence_moving]
    exact h.incompressible t ht (x + t • c)
  · intro t ht x i
    change u t (x + basisVector i + t • c) - c = u t (x + t • c) - c
    rw [show x + basisVector i + t • c = (x + t • c) + basisVector i by abel]
    rw [h.velocity_periodic t ht (x + t • c) i]
  · intro t ht x i
    change p t (x + basisVector i + t • c) = p t (x + t • c)
    rw [show x + basisVector i + t • c = (x + t • c) + basisVector i by abel]
    exact h.pressure_periodic t ht (x + t • c) i

/-- Subtracting any constant mean changes neither the existence question nor
the viscosity.  The inverse direction uses the actual inverse moving frame. -/
theorem exists_periodic_solution_movingDatum_iff (c : Space) (ν : ℝ)
    (u₀ : VelocityField) :
    (∃ u p, IsPeriodicClassicalSolution ν zeroForce (movingDatum c u₀) u p) ↔
      ∃ u p, IsPeriodicClassicalSolution ν zeroForce u₀ u p := by
  constructor
  · rintro ⟨u,p,h⟩
    have hback := isPeriodicClassicalSolution_moving (-c) h
    have hdatum : movingDatum (-c) (movingDatum c u₀) = u₀ := by
      funext x
      simp [movingDatum]
    rw [hdatum] at hback
    exact ⟨_, _, hback⟩
  · rintro ⟨u,p,h⟩
    exact ⟨_, _, isPeriodicClassicalSolution_moving c h⟩

end Navier.Analysis.PeriodicGalileanReduction
