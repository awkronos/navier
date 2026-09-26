import Navier.Analysis.WholeSpaceRestartMildInterface
import Navier.Analysis.EnergyNormBridge

/-!
# Whole-space carrier reconstruction: initial-slice finite energy

`MadelungDecoderCurlObstruction` names the open transport residual: reconstruction
of the continuous Fourier fixed point (`ContinuousLeiLinSpace`) to a
`VelocityEvolution` with **Schwartz initial agreement** and **finite energy**,
preserving the `rawMildViscosity ν₀ / 16` threshold. `WholeSpaceRestartMildInterface`
already closes the agreement half conditionally:
`existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1` consumes exactly two
named premises — the radius smallness `hsmall : restartRadius u₀ ≤ ν / 16` and
the universal-box source regularity `H : ∀ x, SourceL1X1 T (everywhereRawRepresentative ν T x.1)`
— and yields the fixed point with `physicalVelocity (fixedPointTrajectory …) 0 = u₀`.
A fresh whole-file census at this base (`grep` over
`ContinuousLeiLinPhysicalVelocity`, `WholeSpaceRestartMildInterface`,
`ContinuousLeiLinReality`): the carrier had **no energy statement at all**.
The first missing mathematical input of the whole-space carrier is therefore the
finite-energy half of the named residual.

This file closes the smallest slice of that obligation and records the rest.

* `initialSlice_finiteEnergy` — the *constructed* carrier
  `physicalVelocity (fixedPointTrajectory ν hν T (restartRadius u₀) (fourierDatum u₀) x)`
  has finite crown-form energy `Integrable (fun z => ‖· z‖²)` at `t = 0`, for every
  linked-box element and without the two transport premises. It consumes
  `physical_fixedPointTrajectory_fourierDatum_zero` (initial agreement) and the
  inherited-vs-Euclidean bridge `norm_sq_le_sum_sq`; this is the exact shape of the
  `IsClassicalSolution.finite_energy` clause evaluated at the initial slice.
* `initialSlice_euclideanEnergyIntegrable` — the same for the Euclidean density,
  the shape `Navier.kineticEnergy` integrates.
* `initialSlice_kineticEnergy_eq` — the constructed carrier's kinetic-energy
  integral at `t = 0` is *exactly* the datum's initial kinetic-energy density
  integral: the reconstruction is energy-neutral at landing (the Plancherel
  identity of `ContinuousLeiLinPhysicalCarrier` transported onto the carrier).

Exact remaining obligations after this slice (types as measured at this base,
see trailing `#check` output):
1. `SourceL1X1` for every linked-box representative (the named wall — the box
   budgets give only `‖ξ‖⁻¹`-weighted source integrability; the
   `s^(−1/2)·s^(−3/4)` divergence at `τ = 0` is recorded in
   `ContinuousLeiLinMildAssemblyLeaves` above the definition).
2. Every-`t ≥ 0` crown `finite_energy` and `uniformly_bounded_energy` for the
   fixed-point carrier. Note the exponent obstruction: the slot budgets
   `X⁻¹ ∩ X¹` do **not** embed into `L²(ℝ³)` (weight profile `‖ξ‖^(−α)`,
   `α ∈ [3/2, 2)`: in `X⁻¹`, `X¹`, `L¹`, not in `L²`), so energy at `t > 0`
   cannot be a budget corollary — it needs trajectory-specific structure
   (heat decay at `‖ξ‖ → ∞` plus source vanishing at `ξ = 0`), or an explicit
   `L²` slot added to the linked box.
3. Positive-time momentum identity for `physicalVelocity ∘ fixedPointTrajectory`
   (no reality theorem at this base consumes the constructed carrier).
4. The classical-to-continuous-Fourier Duhamel representation plus common-box
   membership, named by the interface header as the remaining restart provider.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Navier.Analysis.WholeSpaceCarrierReconstruction

open Navier
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinActualSlots (ActualLinkedBox)
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum integrable_sq_component)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (physicalVelocity)
open Navier.Analysis.EnergyNormBridge (norm_sq_le_sum_sq)

/-- The constructed initial-slice trajectory: the physical inversion of the
pointwise mild image of a linked-box representative, for the Fourier datum of
a Schwartz trace. -/
def constructedCarrier (ν : NNReal) (hν : 0 < ν) (T : ℝ) (u₀ : SchwartzVelocity)
    (x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀)) :
    VelocityEvolution :=
  physicalVelocity (fixedPointTrajectory ν hν T (restartRadius u₀) (fourierDatum u₀) x)

/-- Coordinate-summed squared density of a Schwartz initial velocity is
integrable on `Space`: three copies of `integrable_sq_component`. -/
private theorem sumSq_integrable (u₀ : SchwartzVelocity) :
    Integrable (fun y : Space => ∑ i : Fin 3, (u₀ y i) ^ 2) volume := by
  have h : (fun y : Space => ∑ i : Fin 3, (u₀ y i) ^ 2) =
      fun y => (u₀ y 0) ^ 2 + ((u₀ y 1) ^ 2 + (u₀ y 2) ^ 2) := by
    funext y
    rw [Fin.sum_univ_three]
    exact add_assoc _ _ _
  rw [h]
  exact (integrable_sq_component u₀ 0).add
    ((integrable_sq_component u₀ 1).add (integrable_sq_component u₀ 2))

/-- **Finite crown-form energy of the reconstructed carrier at the initial
slice.**  For every Schwartz trace and every element of the continuous
whole-space linked box, `Integrable (fun z => ‖constructedCarrier … 0 z‖²)` —
the `IsClassicalSolution.finite_energy` clause evaluated at `t = 0`.  This is
the finite-energy half of the residual named in
`MadelungDecoderCurlObstruction`, discharged at the landing slice: it consumes
the initial-agreement theorem `physical_fixedPointTrajectory_fourierDatum_zero`
and the norm bridge `norm_sq_le_sum_sq`, and needs neither the smallness
premise `hsmall` nor the named wall `SourceL1X1`. -/
theorem initialSlice_finiteEnergy (ν : NNReal) (hν : 0 < ν) (T : ℝ)
    (u₀ : SchwartzVelocity)
    (x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀)) :
    Integrable (fun z : Space =>
      ‖constructedCarrier ν hν T u₀ x 0 z‖ ^ 2) volume := by
  have heq : constructedCarrier ν hν T u₀ x 0 = ⇑u₀ :=
    physical_fixedPointTrajectory_fourierDatum_zero ν hν T (restartRadius u₀) u₀ x
  have hle (z : Space) :
      ‖constructedCarrier ν hν T u₀ x 0 z‖ ^ 2 ≤ ∑ i : Fin 3, (u₀ z i) ^ 2 := by
    rw [congrFun heq z]
    exact norm_sq_le_sum_sq (u₀ z)
  have hae : (fun z : Space => ‖constructedCarrier ν hν T u₀ x 0 z‖ ^ 2) =ᵐ[volume]
      fun z : Space => ‖(u₀ : Space → Space) z‖ ^ 2 :=
    ae_of_all volume fun z => congrArg (fun v : Space => ‖v‖ ^ 2) (congrFun heq z)
  have hmeas : AEStronglyMeasurable
      (fun z : Space => ‖constructedCarrier ν hν T u₀ x 0 z‖ ^ 2) volume :=
    ((u₀.continuous.aestronglyMeasurable).norm.pow 2).congr hae.symm
  have hle' (z : Space) :
      ‖‖constructedCarrier ν hν T u₀ x 0 z‖ ^ 2‖ ≤ ∑ i : Fin 3, (u₀ z i) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle z
  refine (sumSq_integrable u₀).mono' hmeas (ae_of_all volume hle')

/-- The Euclidean density of the reconstructed carrier is integrable at the
initial slice — the integrand whose integral is `Navier.kineticEnergy`. -/
theorem initialSlice_euclideanEnergyIntegrable (ν : NNReal) (hν : 0 < ν) (T : ℝ)
    (u₀ : SchwartzVelocity)
    (x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀)) :
    Integrable (fun y : Space =>
      ∑ i : Fin 3, (constructedCarrier ν hν T u₀ x 0 y i) ^ 2) volume := by
  have hfun : (fun y : Space => ∑ i : Fin 3, (constructedCarrier ν hν T u₀ x 0 y i) ^ 2) =
      fun y : Space => ∑ i : Fin 3, (u₀ y i) ^ 2 := by
    funext y
    refine Finset.sum_congr rfl (fun i _ => congrArg (fun v : ℝ => v ^ 2) ?_)
    exact congrFun (congrFun (physical_fixedPointTrajectory_fourierDatum_zero ν hν T
      (restartRadius u₀) u₀ x) y) i
  rw [hfun]
  exact sumSq_integrable u₀

/-- **Energy neutrality at landing.**  The constructed carrier's kinetic-energy
integral at `t = 0` equals the initial density integral of the Schwartz trace
itself: reconstruction transports the datum's energy exactly, in the
`Navier.kineticEnergy` convention. -/
theorem initialSlice_kineticEnergy_eq (ν : NNReal) (hν : 0 < ν) (T : ℝ)
    (u₀ : SchwartzVelocity)
    (x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀)) :
    Navier.kineticEnergy (constructedCarrier ν hν T u₀ x) 0 =
      ∫ y : Space, ∑ i : Fin 3, (u₀ y i) ^ 2 := by
  show ∫ y : Space, ∑ i : Fin 3, (constructedCarrier ν hν T u₀ x 0 y i) ^ 2 = _
  have hfun : (fun y : Space => ∑ i : Fin 3, (constructedCarrier ν hν T u₀ x 0 y i) ^ 2) =
      fun y : Space => ∑ i : Fin 3, (u₀ y i) ^ 2 := by
    funext y
    refine Finset.sum_congr rfl (fun i _ => congrArg (fun v : ℝ => v ^ 2) ?_)
    exact congrFun (congrFun (physical_fixedPointTrajectory_fourierDatum_zero ν hν T
      (restartRadius u₀) u₀ x) y) i
  rw [hfun]

end Navier.Analysis.WholeSpaceCarrierReconstruction

#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.initialSlice_finiteEnergy
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.initialSlice_euclideanEnergyIntegrable
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.initialSlice_kineticEnergy_eq

set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceCarrierReconstruction.initialSlice_finiteEnergy
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceCarrierReconstruction.initialSlice_kineticEnergy_eq
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.SourceL1X1
set_option pp.fullNames true in
#check @Navier.IsClassicalSolution.finite_energy
