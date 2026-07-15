import Navier.Breakdown.MaximalNonextension

/-!
# Exact force recovery and zero-solution sanity checks

The momentum equation determines the force algebraically from a prescribed
velocity/pressure pair.  This file records that identity for global and
partial solutions, restricts official global solutions to finite intervals,
and supplies the zero partial solution as a non-breakdown sanity witness.

Force recovery alone gives no admissibility or decay theorem for the recovered
force, and the zero solution gives no nonexistence result.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Breakdown.ForceRecovery

open Navier
open Navier.Breakdown

/-- The unique pointwise body force required by a prescribed pair `(u,p)`. -/
def recoveredForce (ν : ℝ) (u : VelocityEvolution)
    (p : PressureEvolution) : ForceField :=
  fun t x =>
    timeDerivative u t x + convection u t x -
      ν • laplacian u t x + pressureGradient p t x

/-- The global momentum equation is equivalent to equality with the recovered
force at every nonnegative time. -/
theorem satisfiesNavierStokes_iff_force_eq_recoveredForce
    (ν : ℝ) (f : ForceField)
    (u : VelocityEvolution) (p : PressureEvolution) :
    SatisfiesNavierStokes ν f u p ↔
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        f t x = recoveredForce ν u p t x := by
  constructor
  · intro h t ht x
    have hx := h t ht x
    simp only [recoveredForce]
    rw [hx]
    abel
  · intro h t ht x
    rw [h t ht x]
    simp only [recoveredForce]
    abel

/-- The same exact force recovery on a certified half-open interval. -/
theorem satisfiesNavierStokesBefore_iff_force_eq_recoveredForce
    (ν : ℝ) (f : ForceField) (T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution) :
    SatisfiesNavierStokesBefore ν f T u p ↔
      ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
        f t x = recoveredForce ν u p t x := by
  constructor
  · intro h t ht htT x
    have hx := h t ht htT x
    simp only [recoveredForce]
    rw [hx]
    abel
  · intro h t ht htT x
    rw [h t ht htT x]
    simp only [recoveredForce]
    abel

end Navier.Breakdown.ForceRecovery

namespace Navier.Breakdown

open Navier

/-- Every official global classical solution restricts to a partial classical
solution on any genuine finite interval. -/
def PartialClassicalSolution.ofClassical
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsClassicalSolution ν f u₀ u p)
    (T : ℝ) (hT : 0 < T) :
    PartialClassicalSolution ν f (fun x => u₀ x) T where
  terminalTime_pos := hT
  velocity := u
  pressure := p
  velocity_smooth := by
    exact h.velocity_smooth.mono (by
      rintro ⟨t, x⟩ ⟨⟨ht0, _htT⟩, hx⟩
      exact ⟨ht0, hx⟩)
  pressure_smooth := by
    exact h.pressure_smooth.mono (by
      rintro ⟨t, x⟩ ⟨⟨ht0, _htT⟩, hx⟩
      exact ⟨ht0, hx⟩)
  initial_condition := by
    funext x
    exact h.initial_condition x
  incompressible := by
    intro t ht _htT x
    exact h.incompressible t ht x
  equation := by
    intro t ht _htT x
    exact h.equation t ht x

/-- The identically zero velocity evolution. -/
def zeroVelocityEvolution : VelocityEvolution := fun _ _ => 0

/-- The identically zero pressure evolution. -/
def zeroPressureEvolution : PressureEvolution := fun _ _ => 0

@[simp] theorem zeroVelocityEvolution_slice (t : ℝ) :
    zeroVelocityEvolution t = 0 := rfl

@[simp] theorem zeroPressureEvolution_slice (t : ℝ) :
    zeroPressureEvolution t = 0 := rfl

/-- The zero pair is a genuine partial classical solution for every viscosity
and positive terminal time. -/
def zeroPartialClassicalSolution
    (ν T : ℝ) (hT : 0 < T) :
    PartialClassicalSolution ν zeroForce (0 : VelocityField) T where
  terminalTime_pos := hT
  velocity := zeroVelocityEvolution
  pressure := zeroPressureEvolution
  velocity_smooth := by
    simp only [SmoothVelocityBefore, zeroVelocityEvolution]
    fun_prop
  pressure_smooth := by
    simp only [SmoothPressureBefore, zeroPressureEvolution]
    fun_prop
  initial_condition := rfl
  incompressible := by
    intro t _ht _htT x
    simp [divergence, spatialDerivative]
  equation := by
    intro t _ht _htT x
    ext i
    simp [timeDerivative, convection, spatialDerivative, laplacian,
      pressureGradient, zeroForce]

/-- The zero partial solution cannot satisfy the point-norm-unbounded producer
required by the checked nonextension consumer. -/
theorem zeroPartial_not_pointNormUnbounded
    (ν T : ℝ) (hT : 0 < T) (x : Space) :
    ¬ (∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      M < ‖(zeroPartialClassicalSolution ν T hT).velocity t x‖) := by
  intro h
  obtain ⟨t, _ht0, _htT, hlarge⟩ := h 0
  simp [zeroPartialClassicalSolution, zeroVelocityEvolution] at hlarge

end Navier.Breakdown
