import Navier.OfficialProblem

/-!
# Conditional observable breakdown below Statements C and D

This file defines a typed consumer for a finite-time classical breakdown
argument.  It is deliberately conditional: it neither constructs a breakdown
witness nor assumes the desired nonexistence conclusion.  The generic consumer
uses an abstract bounded observable.  Its narrower point-evaluation
specialization derives boundedness directly from official global smoothness,
so its producer supplies only an exact solution on `[0, T)`, local uniqueness,
and pointwise norm blowup before `T`.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Navier.Breakdown

/-- The half-open spacetime region on which a partial solution is classical. -/
def spacetimeBefore (T : ℝ) : Set (ℝ × Space) :=
  Set.Ico 0 T ×ˢ Set.univ

/-- Joint spacetime smoothness of a velocity field on `[0, T) × ℝ³`. -/
def SmoothVelocityBefore (T : ℝ) (u : VelocityEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (spacetimeBefore T)

/-- Joint spacetime smoothness of a pressure field on `[0, T) × ℝ³`. -/
def SmoothPressureBefore (T : ℝ) (p : PressureEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (spacetimeBefore T)

/-- Pointwise incompressibility throughout the half-open time interval. -/
def IncompressibleBefore (T : ℝ) (u : VelocityEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space, divergence u t x = 0

/-- The exact official Navier--Stokes equation throughout `[0, T)`. -/
def SatisfiesNavierStokesBefore
    (ν : ℝ) (f : ForceField) (T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Space,
    timeDerivative u t x + convection u t x =
      ν • laplacian u t x - pressureGradient p t x + f t x

/--
A concrete classical velocity/pressure pair on a genuine interval `[0, T)`.
This record contains local PDE data only; it has no maximality or nonexistence
field.
-/
structure PartialClassicalSolution
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ) where
  terminalTime_pos : 0 < T
  velocity : VelocityEvolution
  pressure : PressureEvolution
  velocity_smooth : SmoothVelocityBefore T velocity
  pressure_smooth : SmoothPressureBefore T pressure
  initial_condition : velocity 0 = u₀
  incompressible : IncompressibleBefore T velocity
  equation : SatisfiesNavierStokesBefore ν f T velocity pressure

/-- Equality of velocity time-slices before the candidate breakdown time. -/
def VelocityAgreesBefore
    (T : ℝ) (u v : VelocityEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → u t = v t

/--
Official nonnegative-time smoothness bounds point evaluation on every compact
time interval.  This is the analytic bridge used by the narrower breakdown
consumer below; boundedness is derived rather than stored in its witness.
-/
theorem bounded_pointEvaluation_of_smooth
    {u : VelocityEvolution} {T : ℝ} (x₀ : Space)
    (hT : 0 < T) (hu : SmoothVelocityOnNonnegativeTime u) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖u t x₀‖ ≤ M := by
  have hcontinuous :
      ContinuousOn (fun t : ℝ => ‖u t x₀‖) (Set.Icc 0 T) :=
    (hu.continuousOn.comp
      (Continuous.prodMk_left x₀).continuousOn
      (by
        intro t ht
        exact ⟨ht.1, Set.mem_univ x₀⟩)).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcontinuous
  refine ⟨M, ?_, ?_⟩
  · exact (norm_nonneg (u 0 x₀)).trans
      (hM (Set.mem_image_of_mem _ ⟨le_rfl, hT.le⟩))
  · intro t ht0 htT
    exact hM (Set.mem_image_of_mem _ ⟨ht0, htT⟩)

/--
An observable breakdown certificate relative to a chosen global-solution
predicate.  Its three bridge obligations are independently reusable:
local uniqueness, boundedness for global solutions, and unboundedness of the
partial solution.
-/
structure ObservableBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ)
    (GlobalSolution : VelocityEvolution → PressureEvolution → Prop) where
  localSolution : PartialClassicalSolution ν f u₀ T
  observable : VelocityField → ℝ
  agrees_with_global :
    ∀ u p, GlobalSolution u p →
      VelocityAgreesBefore T localSolution.velocity u
  global_observable_bounded :
    ∀ u p, GlobalSolution u p →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → observable (u t) ≤ M
  partial_observable_unbounded :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      M < observable (localSolution.velocity t)

/-- Direct contradiction transfer from an observable breakdown certificate. -/
theorem noGlobal_of_observableBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : ObservableBreakdownWitness ν f u₀ T GlobalSolution) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution), GlobalSolution u p := by
  rintro ⟨u, p, hglobal⟩
  obtain ⟨M, hbound⟩ := w.global_observable_bounded u p hglobal
  obtain ⟨t, ht0, htT, hlarge⟩ := w.partial_observable_unbounded M
  have hagree := w.agrees_with_global u p hglobal t ht0 htT
  have hle := hbound t ht0 htT
  rw [hagree] at hlarge
  exact (not_lt_of_ge hle) hlarge

/--
A point-evaluation breakdown witness.  Unlike `ObservableBreakdownWitness`,
this record has no global boundedness field: official spacetime smoothness
supplies that bound through `bounded_pointEvaluation_of_smooth`.
-/
structure PointEvaluationBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ)
    (GlobalSolution : VelocityEvolution → PressureEvolution → Prop) where
  localSolution : PartialClassicalSolution ν f u₀ T
  point : Space
  agrees_with_global :
    ∀ u p, GlobalSolution u p →
      VelocityAgreesBefore T localSolution.velocity u
  point_norm_unbounded :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      M < ‖localSolution.velocity t point‖

/--
Generic contradiction transfer when the selected global predicate entails the
official nonnegative-time velocity smoothness contract.
-/
theorem noGlobal_of_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : PointEvaluationBreakdownWitness ν f u₀ T GlobalSolution)
    (global_velocity_smooth :
      ∀ u p, GlobalSolution u p → SmoothVelocityOnNonnegativeTime u) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution), GlobalSolution u p := by
  rintro ⟨u, p, hglobal⟩
  obtain ⟨M, _, hbound⟩ := bounded_pointEvaluation_of_smooth
    w.point w.localSolution.terminalTime_pos
      (global_velocity_smooth u p hglobal)
  obtain ⟨t, ht0, htT, hlarge⟩ := w.point_norm_unbounded M
  have hagree := w.agrees_with_global u p hglobal t ht0 htT
  have hle := hbound t ht0 htT.le
  rw [hagree] at hlarge
  exact (not_lt_of_ge hle) hlarge

/-- Exact specialization to the official whole-space classical predicate. -/
abbrev WholeSpaceObservableBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : SchwartzVelocity) (T : ℝ) :=
  ObservableBreakdownWitness ν f (fun x => u₀ x) T
    (fun u p => IsClassicalSolution ν f u₀ u p)

theorem noWholeSpaceGlobal_of_observableBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (w : WholeSpaceObservableBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν f u₀ u p :=
  noGlobal_of_observableBreakdown w

/-- Point-evaluation breakdown for the official whole-space predicate. -/
abbrev WholeSpacePointEvaluationBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : SchwartzVelocity) (T : ℝ) :=
  PointEvaluationBreakdownWitness ν f (fun x => u₀ x) T
    (fun u p => IsClassicalSolution ν f u₀ u p)

theorem noWholeSpaceGlobal_of_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (w : WholeSpacePointEvaluationBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν f u₀ u p :=
  noGlobal_of_pointEvaluationBreakdown w
    (fun _ _ hglobal => hglobal.velocity_smooth)

/-- Exact specialization to the official periodic classical predicate. -/
abbrev PeriodicObservableBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ) :=
  ObservableBreakdownWitness ν f u₀ T
    (fun u p => IsPeriodicClassicalSolution ν f u₀ u p)

theorem noPeriodicGlobal_of_observableBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (w : PeriodicObservableBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution ν f u₀ u p :=
  noGlobal_of_observableBreakdown w

/-- Point-evaluation breakdown for the official periodic predicate. -/
abbrev PeriodicPointEvaluationBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ) :=
  PointEvaluationBreakdownWitness ν f u₀ T
    (fun u p => IsPeriodicClassicalSolution ν f u₀ u p)

theorem noPeriodicGlobal_of_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    (w : PeriodicPointEvaluationBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution ν f u₀ u p :=
  noGlobal_of_pointEvaluationBreakdown w
    (fun _ _ hglobal => hglobal.velocity_smooth)

end Navier.Breakdown
