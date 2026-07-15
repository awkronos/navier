import Navier.Analysis.EnergyConvectionCancellation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating kinetic energy under the spatial integral

This module gives an interior-time bridge from pointwise differentiation of the
kinetic-energy density to differentiation of its spatial integral.  Its
hypotheses expose the measurability, integrability, and local domination needed
by Mathlib's differentiation-under-the-integral theorem.

The local Lipschitz estimate on `s` supplies a single spatially integrable bound
for the corresponding time difference quotients.  At `t > 0`, `Set.Ici 0` is a
neighborhood of `t`, so the project's right-within derivatives agree with the
ordinary derivatives used by the Mathlib API.  No endpoint statement at `t = 0`
or full energy identity is asserted here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric
open scoped Topology

namespace Navier.Analysis.EnergyDerivativeUnderIntegral

open Navier

/--
At a positive time, the right-within derivative of total kinetic energy is the
integral of the right-within pointwise derivative, provided the density family
is locally Lipschitz in time with one integrable spatial bound.

The set `s` is an explicit time neighborhood on which the Lipschitz domination
holds.  The remaining hypotheses are the measurability and integrability
requirements of `hasDerivAt_integral_of_dominated_loc_of_lip`.
-/
theorem fderivWithin_integral_kineticEnergyDensity_eq_integral_of_dominated
    (u : VelocityEvolution) (t : ℝ) (ht : 0 < t)
    (s : Set ℝ) (bound : Space → ℝ)
    (hs : s ∈ 𝓝 t)
    (hF_meas : ∀ᶠ τ in 𝓝 t,
      AEStronglyMeasurable
        (fun x : Space => kineticEnergyDensity (u τ) x) volume)
    (hF_int : Integrable
      (fun x : Space => kineticEnergyDensity (u t) x) volume)
    (hF'_meas : AEStronglyMeasurable
      (fun x : Space =>
        fderivWithin ℝ
          (fun τ : ℝ => kineticEnergyDensity (u τ) x)
          (Set.Ici 0) t 1) volume)
    (h_lip : ∀ᵐ x : Space ∂volume,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun τ : ℝ => kineticEnergyDensity (u τ) x) s)
    (bound_integrable : Integrable bound volume)
    (h_diff : ∀ᵐ x : Space ∂volume,
      DifferentiableAt ℝ
        (fun τ : ℝ => kineticEnergyDensity (u τ) x) t) :
    Integrable
        (fun x : Space =>
          fderivWithin ℝ
            (fun τ : ℝ => kineticEnergyDensity (u τ) x)
            (Set.Ici 0) t 1) volume ∧
      fderivWithin ℝ
          (fun τ : ℝ =>
            ∫ x : Space, kineticEnergyDensity (u τ) x)
          (Set.Ici 0) t 1 =
        ∫ x : Space,
          fderivWithin ℝ
            (fun τ : ℝ => kineticEnergyDensity (u τ) x)
            (Set.Ici 0) t 1 := by
  have hIci : Set.Ici (0 : ℝ) ∈ 𝓝 t := Ici_mem_nhds ht
  have h_diff' : ∀ᵐ x : Space ∂volume,
      HasDerivAt
        (fun τ : ℝ => kineticEnergyDensity (u τ) x)
        (fderivWithin ℝ
          (fun τ : ℝ => kineticEnergyDensity (u τ) x)
          (Set.Ici 0) t 1) t := by
    filter_upwards [h_diff] with x hx
    simpa only [fderivWithin_of_mem_nhds hIci,
      fderiv_apply_one_eq_deriv] using hx.hasDerivAt
  obtain ⟨hF'_int, hglobal⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_lip
      (F := fun τ x => kineticEnergyDensity (u τ) x)
      (F' := fun x =>
        fderivWithin ℝ
          (fun τ : ℝ => kineticEnergyDensity (u τ) x)
          (Set.Ici 0) t 1)
      (bound := bound) (s := s)
      hs hF_meas hF_int hF'_meas h_lip bound_integrable h_diff'
  refine ⟨hF'_int, ?_⟩
  rw [fderivWithin_of_mem_nhds hIci]
  simpa only [fderiv_apply_one_eq_deriv] using hglobal.deriv

end Navier.Analysis.EnergyDerivativeUnderIntegral
