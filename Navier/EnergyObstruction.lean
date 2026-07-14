import Mathlib
import Navier.Problem

/-!
# Energy-supercritical obstruction theorem

This file proves the genuine real-analysis obstruction that closes the
formalization roadmap's F3-exit "energy-supercritical obstruction" gap
(`docs/FORMALIZATION.md` §4 step 6) and underlies falsification-ledger entry
`F-001`.

**THEOREM (energy is not scale-coercive).** Under the spatial part of the
Navier–Stokes parabolic rescaling `u_c(x) = c · u(c · x)` (the spatial slice of
`u_λ(x,t) = λ u(λ x, λ² t)`), the `L²` kinetic energy rescales by `c⁻¹` while the
scale-critical `L³` quantity is left invariant. Consequently a uniform `L²`
energy bound cannot imply smallness of the scale-critical `L³` quantity: for
every `ε > 0` one can rescale a nonzero field so that its energy is below `ε`
while its critical `L³` mass is unchanged and positive.

This is an obstruction theorem, not a Clay-endpoint claim. It assumes nothing
about the existence or smoothness of a Navier–Stokes solution; it is pure
change-of-variables on `ℝ³`. It is a regression test against accidental
energy-only promotions of regularity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology

namespace Navier.EnergyObstruction

open Navier

/-- The state space `Space = Fin 3 → ℝ` is three real dimensions. -/
theorem space_finrank : Module.finrank ℝ Space = 3 := by
  rw [Module.finrank_fin_fun]

/-- The `L²` kinetic energy of the rescaled field `c · u(c · ·)` is `c⁻¹` times
the original energy. -/
theorem l2_energy_dilation (c : ℝ) (hc : 0 < c) (u : Space → Space) :
    ∫ x, ‖c • u (c • x)‖^2 ∂volume = c⁻¹ • ∫ x, ‖u x‖^2 ∂volume := by
  have hu : ∀ y, ‖c • u y‖^2 = c^2 • ‖u y‖^2 := fun y => by
    have h : ‖c • u y‖ = c * ‖u y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    rw [h]; simp only [smul_eq_mul]; ring
  have hci : 0 < (c ^ 3)⁻¹ := by positivity
  simp only [hu, integral_smul,
    MeasureTheory.Measure.integral_comp_smul volume (fun x => ‖u x‖^2) c,
    Module.finrank_fin_fun, abs_of_pos hci]
  rw [smul_smul]; congr 1; field_simp

/-- The scale-critical `L³` quantity is invariant under the rescaling. -/
theorem l3_critical_dilation (c : ℝ) (hc : 0 < c) (u : Space → Space) :
    ∫ x, ‖c • u (c • x)‖^3 ∂volume = ∫ x, ‖u x‖^3 ∂volume := by
  have hu : ∀ y, ‖c • u y‖^3 = c^3 • ‖u y‖^3 := fun y => by
    have h : ‖c • u y‖ = c * ‖u y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    rw [h]; simp only [smul_eq_mul]; ring
  have hci : 0 < (c ^ 3)⁻¹ := by positivity
  simp only [hu, integral_smul,
    MeasureTheory.Measure.integral_comp_smul volume (fun x => ‖u x‖^3) c,
    Module.finrank_fin_fun, abs_of_pos hci]
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hc.ne'), one_smul]

/-- For every `ε > 0` there is a rescaling whose `L²` energy is below `ε` while
its scale-critical `L³` mass stays equal to the original **and remains
positive**.

This is the obstruction: the `L²` energy can be made arbitrarily small by
parabolic rescaling while the scale-critical `L³` quantity does not move. Hence
no uniform `L²` energy bound can control the scale-critical `L³` quantity, and
energy alone is not scale-coercive.

Hypotheses: `φ` is a field in `L² ∩ L³` with strictly positive `L³` mass (i.e. a
genuine nonzero datum). These are exact, concrete hypotheses — not the endpoint
and not a continuation criterion. -/
theorem energy_not_scale_coercive
    (φ : Space → Space)
    (_hφ2 : Integrable (fun x => ‖φ x‖^2) volume)
    (_hφ3 : Integrable (fun x => ‖φ x‖^3) volume)
    (hφ3pos : 0 < ∫ x, ‖φ x‖^3 ∂volume) :
    ∀ ε > 0, ∃ c : ℝ, 0 < c ∧
      ∫ x, ‖c • φ (c • x)‖^2 ∂volume < ε ∧
      ∫ x, ‖c • φ (c • x)‖^3 ∂volume = ∫ x, ‖φ x‖^3 ∂volume ∧
      0 < ∫ x, ‖c • φ (c • x)‖^3 ∂volume := by
  intro ε hε
  set A2 := ∫ x, ‖φ x‖^2 ∂volume
  have hA2 : 0 ≤ A2 := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨A2 / ε + 1, by positivity, ?_, ?_, ?_⟩
  · rw [l2_energy_dilation _ (by positivity) φ, smul_eq_mul]
    have hd : 0 < A2 / ε + 1 := by positivity
    rw [← div_eq_inv_mul, div_lt_iff₀ hd]; field_simp; linarith
  · exact l3_critical_dilation _ (by positivity) φ
  · rw [l3_critical_dilation _ (by positivity) φ]; exact hφ3pos

end Navier.EnergyObstruction
