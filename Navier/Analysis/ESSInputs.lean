import Navier.Analysis.CriticalLp
import Navier.Breakdown.MaximalNonextension

/-!
# Measurable critical slices below the ESS bridge

Joint smoothness of a partial classical solution makes every certified spatial
velocity and pressure slice continuous, hence strongly measurable.  This file
connects those real solution slices to the faithful `MemLp`/cubic-density
interface.

It constructs no endpoint trace, critical bound, suitable weak solution,
backward-uniqueness theorem, or continuation result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Navier.Analysis.ESSInputs

open Navier
open Navier.Breakdown
open Navier.Analysis.CriticalLp

/-- Every velocity slice strictly before the terminal time is continuous on
all of space. -/
theorem PartialClassicalSolution.velocity_slice_continuous
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T t : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (ht0 : 0 ≤ t) (htT : t < T) :
    Continuous (sol.velocity t) := by
  rw [← continuousOn_univ]
  exact sol.velocity_smooth.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (by
      intro x _hx
      exact ⟨⟨ht0, htT⟩, Set.mem_univ x⟩)

/-- Every pressure slice strictly before the terminal time is continuous on
all of space. -/
theorem PartialClassicalSolution.pressure_slice_continuous
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T t : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (ht0 : 0 ≤ t) (htT : t < T) :
    Continuous (sol.pressure t) := by
  rw [← continuousOn_univ]
  exact sol.pressure_smooth.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (by
      intro x _hx
      exact ⟨⟨ht0, htT⟩, Set.mem_univ x⟩)

theorem PartialClassicalSolution.velocity_slice_aestronglyMeasurable
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T t : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (ht0 : 0 ≤ t) (htT : t < T) :
    AEStronglyMeasurable (sol.velocity t) volume :=
  velocity_slice_continuous sol ht0 htT |>.aestronglyMeasurable

theorem PartialClassicalSolution.pressure_slice_aestronglyMeasurable
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T t : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (ht0 : 0 ≤ t) (htT : t < T) :
    AEStronglyMeasurable (sol.pressure t) volume :=
  pressure_slice_continuous sol ht0 htT |>.aestronglyMeasurable

/-- On a genuine partial-solution slice, `L^3` membership is exactly the
integrability of the cubic norm density; measurability is derived rather than
assumed. -/
theorem PartialClassicalSolution.velocity_slice_memLp_three_iff
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T t : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (ht0 : 0 ≤ t) (htT : t < T) :
    MemLp (sol.velocity t) 3 volume ↔
      Integrable (fun x : Space => ‖sol.velocity t x‖ ^ 3) volume :=
  memLp_three_iff_integrable_norm_cube
    (velocity_slice_aestronglyMeasurable sol ht0 htT)

end Navier.Analysis.ESSInputs
