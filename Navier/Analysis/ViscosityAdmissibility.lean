import Navier.Analysis.ViscosityTransport

/-!
# Admissibility and solution-contract transport across viscosity

This module extends the pointwise identities in `ViscosityTransport` to the
smoothness, initial-data, incompressibility, periodicity, and energy fields of
the official whole-space and periodic solution contracts.

For `a > 0`, the spacetime map `(t,x) ↦ (a*t,x)` preserves the closed
nonnegative-time half-space.  Composing with this smooth map and multiplying
the codomain by a constant transports the `ContDiffOn` fields.  The spatial
energy integral gains the exact factor `a^2`, so integrability and a uniform
positive bound are preserved as well.

The resulting theorems transport complete `IsClassicalSolution` and
`IsPeriodicClassicalSolution` witnesses.  They do not assert that an arbitrary
rapid-decay force remains in `ForcedDataRapidDecay` or
`PeriodicForcedDataRapidDecay`; only the exact zero-force instances are closed
here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Navier.Analysis.ViscosityAdmissibility

open Navier
open ViscosityTransport

/-- The spacetime map used by viscosity transport. -/
def viscosityTimeMap (a : ℝ) : ℝ × Space → ℝ × Space :=
  fun z ↦ (a * z.1, z.2)

/-- The viscosity time map is smooth on all spacetime. -/
theorem contDiff_viscosityTimeMap (a : ℝ) :
    ContDiff ℝ ∞ (viscosityTimeMap a) :=
  (contDiff_fst.const_smul a).prodMk contDiff_snd

/-- A positive time dilation preserves the closed nonnegative-time
spacetime set. -/
theorem mapsTo_nonnegativeSpacetime_viscosityTimeMap
    (a : ℝ) (ha : 0 < a) :
    Set.MapsTo (viscosityTimeMap a) nonnegativeSpacetime
      nonnegativeSpacetime := by
  intro z hz
  rcases hz with ⟨ht, hx⟩
  exact ⟨mul_nonneg ha.le ht, hx⟩

/-- Positive viscosity transport preserves the half-space smoothness of
velocity. -/
theorem smoothVelocity_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution)
    (hu : SmoothVelocityOnNonnegativeTime u) :
    SmoothVelocityOnNonnegativeTime (viscosityScaledVelocity a u) := by
  have hcomp :=
    hu.comp (contDiff_viscosityTimeMap a).contDiffOn
      (mapsTo_nonnegativeSpacetime_viscosityTimeMap a ha)
  have hscaled := hcomp.const_smul a
  simpa only [SmoothVelocityOnNonnegativeTime, nonnegativeSpacetime,
    viscosityScaledVelocity, viscosityTimeMap, Function.comp_apply] using
    hscaled

/-- Positive viscosity transport preserves the half-space smoothness of
pressure. -/
theorem smoothPressure_viscosityScaled
    (a : ℝ) (ha : 0 < a) (p : PressureEvolution)
    (hp : SmoothPressureOnNonnegativeTime p) :
    SmoothPressureOnNonnegativeTime (viscosityScaledPressure a p) := by
  have hcomp :=
    hp.comp (contDiff_viscosityTimeMap a).contDiffOn
      (mapsTo_nonnegativeSpacetime_viscosityTimeMap a ha)
  have hscaled := hcomp.const_smul (a ^ 2)
  simpa only [SmoothPressureOnNonnegativeTime, nonnegativeSpacetime,
    viscosityScaledPressure, viscosityTimeMap, Function.comp_apply,
    smul_eq_mul] using hscaled

/-- Positive viscosity transport preserves the half-space smoothness of a
force. -/
theorem smoothForce_viscosityScaled
    (a : ℝ) (ha : 0 < a) (f : ForceField)
    (hf : SmoothForceOnNonnegativeTime f) :
    SmoothForceOnNonnegativeTime (viscosityScaledForce a f) := by
  have hcomp :=
    hf.comp (contDiff_viscosityTimeMap a).contDiffOn
      (mapsTo_nonnegativeSpacetime_viscosityTimeMap a ha)
  have hscaled := hcomp.const_smul (a ^ 2)
  simpa only [SmoothForceOnNonnegativeTime, nonnegativeSpacetime,
    viscosityScaledForce, viscosityTimeMap, Function.comp_apply] using hscaled

/-- Squared norms gain the exact factor `a^2` under positive scalar
multiplication. -/
theorem norm_sq_smul (a : ℝ) (ha : 0 < a) (v : Space) :
    ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  ring

/-- Kinetic energy gains the exact factor `a^2`; only time, not space, is
rescaled. -/
theorem kineticEnergy_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution) (t : ℝ) :
    kineticEnergy (viscosityScaledVelocity a u) t =
      a ^ 2 * kineticEnergy u (a * t) := by
  simp only [kineticEnergy, viscosityScaledVelocity, norm_sq_smul a ha]
  rw [integral_const_mul]

/-- Spatial energy integrability is preserved at corresponding times. -/
theorem finiteEnergy_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution) (t : ℝ)
    (h : Integrable (fun x : Space ↦ ‖u (a * t) x‖ ^ 2)) :
    Integrable
      (fun x : Space ↦ ‖viscosityScaledVelocity a u t x‖ ^ 2) := by
  have hs := h.const_mul (a ^ 2)
  simpa only [viscosityScaledVelocity, norm_sq_smul a ha] using hs

/-- A uniform positive energy bound transports with factor `a^2`. -/
theorem uniformEnergy_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution)
    (h : ∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E) :
    ∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t →
        kineticEnergy (viscosityScaledVelocity a u) t < E := by
  rcases h with ⟨E, hE, hbound⟩
  refine ⟨a ^ 2 * E, mul_pos (sq_pos_of_pos ha) hE, ?_⟩
  intro t ht
  rw [kineticEnergy_viscosityScaled a ha]
  exact mul_lt_mul_of_pos_left
    (hbound (a * t) (mul_nonneg ha.le ht)) (sq_pos_of_pos ha)

/-- Complete periodic classical solutions transport from viscosity `mu` to
viscosity `a * mu`. -/
theorem isPeriodicClassicalSolution_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu : ℝ) (f : ForceField)
    (u₀ : VelocityField) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsPeriodicClassicalSolution mu f u₀ u p) :
    IsPeriodicClassicalSolution (a * mu) (viscosityScaledForce a f)
      (viscosityScaledDatum a u₀) (viscosityScaledVelocity a u)
      (viscosityScaledPressure a p) where
  velocity_smooth := smoothVelocity_viscosityScaled a ha u h.velocity_smooth
  pressure_smooth := smoothPressure_viscosityScaled a ha p h.pressure_smooth
  initial_condition :=
    initialCondition_viscosityScaled a u₀ u h.initial_condition
  incompressible := incompressible_viscosityScaled a ha u h.incompressible
  equation :=
    satisfiesNavierStokes_viscosityScaled_mul a ha mu f u p h.equation
  velocity_periodic :=
    spatiallyPeriodicVelocity_viscosityScaled a ha u h.velocity_periodic
  pressure_periodic :=
    spatiallyPeriodicPressure_viscosityScaled a ha p h.pressure_periodic

/-- Complete whole-space classical solutions transport from viscosity `mu`
to viscosity `a * mu`. -/
theorem isClassicalSolution_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu : ℝ) (f : ForceField)
    (u₀ : SchwartzVelocity) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsClassicalSolution mu f u₀ u p) :
    IsClassicalSolution (a * mu) (viscosityScaledForce a f)
      (viscosityScaledSchwartzDatum a u₀) (viscosityScaledVelocity a u)
      (viscosityScaledPressure a p) where
  velocity_smooth := smoothVelocity_viscosityScaled a ha u h.velocity_smooth
  pressure_smooth := smoothPressure_viscosityScaled a ha p h.pressure_smooth
  initial_condition :=
    initialCondition_viscosityScaledSchwartz a u₀ u h.initial_condition
  incompressible := incompressible_viscosityScaled a ha u h.incompressible
  equation :=
    satisfiesNavierStokes_viscosityScaled_mul a ha mu f u p h.equation
  finite_energy := fun t ht ↦
    finiteEnergy_viscosityScaled a ha u t
      (h.finite_energy (a * t) (mul_nonneg ha.le ht))
  uniformly_bounded_energy :=
    uniformEnergy_viscosityScaled a ha u h.uniformly_bounded_energy

/-- Viscosity-one periodic solutions transport to every positive
viscosity. -/
theorem isPeriodicClassicalSolution_one_to_viscosity
    (nu : ℝ) (hnu : 0 < nu) (f : ForceField)
    (u₀ : VelocityField) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsPeriodicClassicalSolution 1 f u₀ u p) :
    IsPeriodicClassicalSolution nu (viscosityScaledForce nu f)
      (viscosityScaledDatum nu u₀) (viscosityScaledVelocity nu u)
      (viscosityScaledPressure nu p) := by
  simpa only [mul_one] using
    isPeriodicClassicalSolution_viscosityScaled_mul
      nu hnu 1 f u₀ u p h

/-- Viscosity-one whole-space solutions transport to every positive
viscosity. -/
theorem isClassicalSolution_one_to_viscosity
    (nu : ℝ) (hnu : 0 < nu) (f : ForceField)
    (u₀ : SchwartzVelocity) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsClassicalSolution 1 f u₀ u p) :
    IsClassicalSolution nu (viscosityScaledForce nu f)
      (viscosityScaledSchwartzDatum nu u₀) (viscosityScaledVelocity nu u)
      (viscosityScaledPressure nu p) := by
  simpa only [mul_one] using
    isClassicalSolution_viscosityScaled_mul nu hnu 1 f u₀ u p h

/-- Positive-viscosity periodic solutions transport back to viscosity one. -/
theorem isPeriodicClassicalSolution_viscosity_to_one
    (nu : ℝ) (hnu : 0 < nu) (f : ForceField)
    (u₀ : VelocityField) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsPeriodicClassicalSolution nu f u₀ u p) :
    IsPeriodicClassicalSolution 1 (viscosityScaledForce nu⁻¹ f)
      (viscosityScaledDatum nu⁻¹ u₀) (viscosityScaledVelocity nu⁻¹ u)
      (viscosityScaledPressure nu⁻¹ p) := by
  have hnuInv : 0 < nu⁻¹ := inv_pos.mpr hnu
  simpa only [inv_mul_cancel₀ hnu.ne'] using
    isPeriodicClassicalSolution_viscosityScaled_mul
      nu⁻¹ hnuInv nu f u₀ u p h

/-- Positive-viscosity whole-space solutions transport back to viscosity
one. -/
theorem isClassicalSolution_viscosity_to_one
    (nu : ℝ) (hnu : 0 < nu) (f : ForceField)
    (u₀ : SchwartzVelocity) (u : VelocityEvolution) (p : PressureEvolution)
    (h : IsClassicalSolution nu f u₀ u p) :
    IsClassicalSolution 1 (viscosityScaledForce nu⁻¹ f)
      (viscosityScaledSchwartzDatum nu⁻¹ u₀)
      (viscosityScaledVelocity nu⁻¹ u)
      (viscosityScaledPressure nu⁻¹ p) := by
  have hnuInv : 0 < nu⁻¹ := inv_pos.mpr hnu
  simpa only [inv_mul_cancel₀ hnu.ne'] using
    isClassicalSolution_viscosityScaled_mul
      nu⁻¹ hnuInv nu f u₀ u p h

/-- The zero force satisfies the complete whole-space rapid-decay predicate. -/
theorem forcedDataRapidDecay_zeroForce : ForcedDataRapidDecay zeroForce := by
  constructor
  · exact contDiff_const.contDiffOn
  · intro n K
    refine ⟨0, le_rfl, ?_⟩
    intro t ht x
    simp [zeroForce]

/-- The zero force satisfies the complete periodic time-decay predicate. -/
theorem periodicForcedDataRapidDecay_zeroForce :
    PeriodicForcedDataRapidDecay zeroForce := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x i
    rfl
  · exact contDiff_const.contDiffOn
  · intro n K
    refine ⟨0, le_rfl, ?_⟩
    intro t ht x
    simp [zeroForce]

end Navier.Analysis.ViscosityAdmissibility
