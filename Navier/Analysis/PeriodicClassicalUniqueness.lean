import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.ViscosityAdmissibility
import Navier.Construction.PeriodicUniqueness

/-!
# Uniqueness on the official periodic carrier

The periodic energy argument in `Construction.PeriodicUniqueness` is stated on
the Euclidean presentation used by the construction.  The repository's
alternative-B contract is stated on the same three coordinates with the product
norm and requires periodic velocity and a periodic pressure representative.
This module transports that exact contract through the proved coordinate
equivalence and applies the energy argument on every compact time slab.

This closes the uniqueness consequence of alternative B.  It does not supply
the existence assertion in `ProblemStatements.PeriodicGlobalRegularity`.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff

namespace Navier.Analysis.PeriodicClassicalUniqueness

open Set
open Navier
open Navier.Analysis.EuclideanPDETransport
open Navier.Construction.ProblemStatement

private theorem euclideanVelocity_periodic
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν f u₀ u p)
    {a b : ℝ} (ha : 0 ≤ a) :
    UnitSpatialPeriodsOn (Icc a b) (euclideanVelocity u) := by
  intro t ht x i
  have hp := h.velocity_periodic t (ha.trans ht.1) (toNative x) i
  have hcoord : toNative (coordinateVector i) = basisVector i := by
    exact toNative_eBasisVector i
  simpa [euclideanVelocity, map_add, hcoord] using
    congrArg EuclideanPDETransport.toEuclidean hp

private theorem euclideanPressure_periodic
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν f u₀ u p)
    {a b : ℝ} (ha : 0 ≤ a) :
    UnitSpatialPeriodsOn (Icc a b) (euclideanPressure p) := by
  intro t ht x i
  have hcoord : toNative (coordinateVector i) = basisVector i := by
    exact toNative_eBasisVector i
  simpa [euclideanPressure, map_add, hcoord] using
    h.pressure_periodic t (ha.trans ht.1) (toNative x) i

private theorem euclideanVelocity_divergenceFree
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution ν f u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ x, spatialDivergence (euclideanVelocity u) t x = 0 := by
  intro x
  have hs := eFutureSpatialSlice_contDiff
    (euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth) ht
  have hd := divergence_nativeVelocity (euclideanVelocity u)
    (x := x) (hs.differentiable (by simp) x)
  rw [nativeVelocity_euclideanVelocity] at hd
  exact hd.symm.trans (h.incompressible t ht (toNative x))

private theorem euclideanVelocity_residual_zero
    {u₀ : VelocityField} {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsPeriodicClassicalSolution 1 zeroForce u₀ u p)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, navierStokesResidual (euclideanVelocity u) (euclideanPressure p) t x = 0 := by
  intro x
  have hs := eFutureSpatialSlice_contDiff
    (euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth) ht.le
  have hps := eFuturePressureSlice_contDiff
    (euclideanPressure_smoothOnNonnegativeTime h.pressure_smooth) ht.le
  have htime := eFutureTimeSlice_differentiableAt
    (euclideanVelocity_smoothOnNonnegativeTime h.velocity_smooth) ht x
  have ht' := timeDerivative_nativeVelocity_of_pos (euclideanVelocity u) ht x htime
  have hc := convection_nativeVelocity (euclideanVelocity u)
    (x := x) (hs.differentiable (by simp) x)
  have hl := laplacian_nativeVelocity (euclideanVelocity u) (x := x) hs
  have hp' := pressureGradient_nativePressure (euclideanPressure p) (x := x)
    (hps.differentiable (by simp) x)
  apply toNative.injective
  change toNative
      (eTimeDerivative (euclideanVelocity u) t x +
        eConvection (euclideanVelocity u) t x -
        eLaplacian (euclideanVelocity u) t x +
        ePressureGradient (euclideanPressure p) t x) = toNative 0
  simp only [map_add, map_sub, map_zero]
  rw [← ht', ← hc, ← hl, ← hp']
  rw [nativeVelocity_euclideanVelocity, nativePressure_euclideanPressure]
  have hNS := h.equation t ht.le (toNative x)
  simpa [zeroForce] using congrArg (fun z => z - laplacian u t (toNative x) +
    pressureGradient p t (toNative x)) hNS

/-- Two solutions of the repository's periodic classical contract at viscosity
one, with the same initial datum, have identical velocities for every
nonnegative time.  Both hypotheses include a periodic pressure representative.
Pressure itself is deliberately not identified: the equation determines it
only up to a space-constant gauge. -/
theorem velocity_unique_at_viscosity_one
    {u₀ : VelocityField}
    {u v : VelocityEvolution} {p q : PressureEvolution}
    (hu : IsPeriodicClassicalSolution 1 zeroForce u₀ u p)
    (hv : IsPeriodicClassicalSolution 1 zeroForce u₀ v q) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, u t x = v t x := by
  intro t ht x
  have hsub : Navier.Construction.PeriodicUniqueness.slab 0 t ⊆ eFutureDomain := by
    intro z hz
    exact ⟨hz.1.1, mem_univ _⟩
  have hEU := euclideanVelocity_smoothOnNonnegativeTime hu.velocity_smooth
  have hEV := euclideanVelocity_smoothOnNonnegativeTime hv.velocity_smooth
  have hEP := euclideanPressure_smoothOnNonnegativeTime hu.pressure_smooth
  have hEQ := euclideanPressure_smoothOnNonnegativeTime hv.pressure_smooth
  have hunique := Navier.Construction.PeriodicUniqueness.classical_uniqueness_on_Icc
    (f := fun _ => 0)
    (hEU.mono hsub) (hEV.mono hsub) (hEP.mono hsub) (hEQ.mono hsub)
    (euclideanVelocity_periodic hu le_rfl)
    (euclideanVelocity_periodic hv le_rfl)
    (euclideanPressure_periodic hu le_rfl)
    (euclideanPressure_periodic hv le_rfl)
    (fun s hs ↦ euclideanVelocity_divergenceFree hu hs.1.le)
    (fun s hs ↦ euclideanVelocity_divergenceFree hv hs.1.le)
    (fun s hs ↦ euclideanVelocity_residual_zero hu hs.1)
    (fun s hs ↦ euclideanVelocity_residual_zero hv hs.1)
    (fun y ↦ by simp [euclideanVelocity, hu.initial_condition, hv.initial_condition])
  have he := hunique t ⟨ht, le_rfl⟩ (toEuclidean x)
  simpa [euclideanVelocity] using congrArg toNative he

/-- The same uniqueness statement at every positive viscosity.  This uses the
repository's exact viscosity transport to normalize both solutions to
viscosity one, applies the preceding physical-space energy theorem, and then
cancels the common positive scaling. -/
theorem velocity_unique
    {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField}
    {u v : VelocityEvolution} {p q : PressureEvolution}
    (hu : IsPeriodicClassicalSolution ν zeroForce u₀ u p)
    (hv : IsPeriodicClassicalSolution ν zeroForce u₀ v q) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, u t x = v t x := by
  intro t ht x
  have hu1 :=
    Navier.Analysis.ViscosityAdmissibility.isPeriodicClassicalSolution_viscosity_to_one
      ν hν zeroForce u₀ u p hu
  have hv1 :=
    Navier.Analysis.ViscosityAdmissibility.isPeriodicClassicalSolution_viscosity_to_one
      ν hν zeroForce u₀ v q hv
  have hu1' : IsPeriodicClassicalSolution 1 zeroForce
      (Navier.Analysis.ViscosityTransport.viscosityScaledDatum ν⁻¹ u₀)
      (Navier.Analysis.ViscosityTransport.viscosityScaledVelocity ν⁻¹ u)
      (Navier.Analysis.ViscosityTransport.viscosityScaledPressure ν⁻¹ p) := by
    simpa [Navier.Analysis.ViscosityTransport.viscosityScaledForce, zeroForce] using hu1
  have hv1' : IsPeriodicClassicalSolution 1 zeroForce
      (Navier.Analysis.ViscosityTransport.viscosityScaledDatum ν⁻¹ u₀)
      (Navier.Analysis.ViscosityTransport.viscosityScaledVelocity ν⁻¹ v)
      (Navier.Analysis.ViscosityTransport.viscosityScaledPressure ν⁻¹ q) := by
    simpa [Navier.Analysis.ViscosityTransport.viscosityScaledForce, zeroForce] using hv1
  have he := velocity_unique_at_viscosity_one hu1' hv1'
    (ν * t) (mul_nonneg hν.le ht) x
  have hscaled := congrArg (fun z : Space => ν • z) he
  simpa [Navier.Analysis.ViscosityTransport.viscosityScaledVelocity,
    smul_smul, hν.ne'] using hscaled

/-- The repository's exact alternative B, if established, supplies a velocity
that is unique among solutions of its periodic classical contract with the same
datum.  This is a direct consumer of `PeriodicGlobalRegularity`; its existence
premise remains visible and is not discharged here. -/
theorem periodicGlobalRegularity_uniqueVelocity
    (hB : ProblemStatements.PeriodicGlobalRegularity) :
    ∀ ν : ℝ, 0 < ν →
      ∀ u₀ : VelocityField, PeriodicInitialDatum u₀ →
        ∃ (u : VelocityEvolution) (p : PressureEvolution),
          IsPeriodicClassicalSolution ν zeroForce u₀ u p ∧
          ∀ (v : VelocityEvolution) (q : PressureEvolution),
            IsPeriodicClassicalSolution ν zeroForce u₀ v q →
              ∀ t : ℝ, 0 ≤ t → ∀ x : Space, u t x = v t x := by
  intro ν hν u₀ hu₀
  obtain ⟨u, p, hu⟩ := hB ν hν u₀ hu₀
  exact ⟨u, p, hu, fun v q hv => velocity_unique hν hu hv⟩

end Navier.Analysis.PeriodicClassicalUniqueness
