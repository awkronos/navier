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

Free heat carrier (`warm-continue slice, same lane`):

* `freeHeatTraj` — the frequency-side free evolution `t ↦ heatVec ν t (fourierDatum u₀)`.
* `norm_freeHeatCoord_le` — for `0 ≤ ν`, `0 ≤ t` the Gaussian multiplier obeys
  `exp(-(ν‖ξ‖²t)) ≤ 1`, so every frequency coordinate contracts pointwise.
* `integral_normSq_freeHeatCoord_le`, `sum_integral_normSq_freeHeat_le_initial` —
  the free carrier's frequency-side L²-mass per coordinate and in total is
  dominated by the initial datum's energy for EVERY `t ≥ 0`.
* `freeHeatPhysical_finiteEnergy_of_schwartz` — the crown-form physical-space
  integrability `Integrable (fun z => ‖physicalVelocity (freeHeatTraj ν u₀) t z‖²)`
  at every `t ≥ 0`, conditional on exactly one named input: Schwartz-space
  membership of the Gaussian multiplier slices. That membership is equivalent
  (via `SchwartzMap.bilinLeftCLM` with `Complex.mulL`) to
  `Function.HasTemperateGrowth (fun ξ : ES => (Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℂ))`,
  which this Mathlib rev does NOT carry (measured by source grep: the
  Gaussian files are contour-integral only; `SchwartzSpace` has no
  `Mul`/`gaussian`/`exp`-membership API; the repo proves heat-kernel spatial
  derivatives only up to order two, in physical space, in
  `HeatSemigroupSmoothing`). The free side is therefore ONE Mathlib-level API
  entry away from unconditional crown-form energy at every `t ≥ 0`; the
  Duhamel (nonlinear) addition remains the wall.

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
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum integrable_sq_component
  physicalCoord fourierDatum_energy_eq_physical)
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

/-! ## Free heat carrier: energy at every `t ≥ 0` -/

open Navier.Analysis.ContinuousLeiLinSpace (ES ComplexSpace heatMode)
open Navier.Analysis.ContinuousLeiLinDissipation (heatVec)
open Navier.Analysis.FourierMajorant (euclidComponent)
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)

/-- The **free** heat trajectory of a Schwartz datum on the continuous
Fourier carrier: `t ↦ heatVec ν t (fourierDatum u₀)`, coordinatewise
`exp(-(ν‖ξ‖²t)) · ̂u₀ᵢ(ξ)`. -/
def freeHeatTraj (ν : ℝ) (u₀ : SchwartzVelocity) : ℝ → ES → ComplexSpace :=
  fun t => heatVec ν t (fourierDatum u₀)

theorem freeHeatCoord_eq (ν t : ℝ) (u₀ : SchwartzVelocity) (ξ : ES) (i : Fin 3) :
    heatVec ν t (fourierDatum u₀) ξ i =
      (↑(Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * fourierDatum u₀ ξ i := rfl

/-- **Pointwise contraction of the Gaussian multiplier.**  For `0 ≤ ν`,
`0 ≤ t`, the heat factor is `≤ 1`, so every frequency coordinate of the free
carrier is dominated pointwise by the datum's. -/
theorem norm_freeHeatCoord_le (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) (u₀ : SchwartzVelocity)
    (ξ : ES) (i : Fin 3) :
    ‖heatVec ν t (fourierDatum u₀) ξ i‖ ≤ ‖fourierDatum u₀ ξ i‖ := by
  have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 := by
    have h : -(ν * ‖ξ‖ ^ 2 * t) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (mul_nonneg hν (sq_nonneg _)) ht)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr h
  rw [freeHeatCoord_eq, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)).trans (one_mul _).le

theorem integral_normSq_freeHeatCoord_le (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u₀ : SchwartzVelocity) (i : Fin 3) :
    (∫ ξ : ES, ‖heatVec ν t (fourierDatum u₀) ξ i‖ ^ 2) ≤
      ∫ ξ : ES, ‖fourierDatum u₀ ξ i‖ ^ 2 := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : ES => ‖heatVec ν t (fourierDatum u₀) ξ i‖ ^ 2) volume := by
    have hn : Continuous (fun ξ : ES => ‖ξ‖ ^ 2) := (continuous_norm (E := ES)).pow 2
    have h1 : Continuous (fun ξ : ES => -(ν * ‖ξ‖ ^ 2 * t)) :=
      Continuous.neg ((continuous_const.mul hn).mul continuous_const)
    have h2 : Continuous (fun ξ : ES => (↑(Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)) :=
      Continuous.comp Complex.continuous_ofReal (Real.continuous_exp.comp h1)
    have h3 : Continuous (fun ξ : ES => fourierDatum u₀ ξ i) :=
      (SchwartzMap.fourierTransformCLM ℂ (euclidComponent u₀ i)).continuous
    have hfun : (fun ξ : ES => ‖heatVec ν t (fourierDatum u₀) ξ i‖ ^ 2) =
        (fun ξ : ES => ‖(↑(Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * fourierDatum u₀ ξ i‖ ^ 2) := by
      funext ξ
      rw [freeHeatCoord_eq ν t u₀ ξ i]
    rw [hfun]
    exact ((h2.mul h3).aestronglyMeasurable).norm.pow 2
  have hdom : Integrable (fun ξ : ES => ‖fourierDatum u₀ ξ i‖ ^ 2) volume :=
    ((SchwartzMap.fourierTransformCLM ℂ (euclidComponent u₀ i)).memLp 2 volume).integrable_norm_pow
      (by norm_num)
  have hint_f : Integrable (fun ξ : ES => ‖heatVec ν t (fourierDatum u₀) ξ i‖ ^ 2) volume :=
    hdom.mono' hmeas (ae_of_all volume fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_freeHeatCoord_le ν t hν ht u₀ ξ i) 2)
  refine integral_mono hint_f hdom fun ξ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_freeHeatCoord_le ν t hν ht u₀ ξ i) 2

/-- **Unconditional every-`t ≥ 0` frequency-side energy domination of the
free carrier**: the total squared `L²`-mass of `heatVec ν t (fourierDatum u₀)`
is at most the initial datum's energy for every `t ≥ 0` (Plancherel closes
the right side exactly). -/
theorem sum_integral_normSq_freeHeat_le_initial (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u₀ : SchwartzVelocity) :
    (∑ i : Fin 3, ∫ ξ : ES, ‖heatVec ν t (fourierDatum u₀) ξ i‖ ^ 2) ≤
      ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun i _ =>
    integral_normSq_freeHeatCoord_le ν t hν ht u₀ i) ?_
  exact (fourierDatum_energy_eq_physical u₀).le

/-- Euclidean transport of a Schwartz `L²` bound to `Space` along
`euclidPoint` (the `WienerLocalClassical` idiom, copied so this file stays
import-light). -/
private theorem integrable_euclid_sq (s : SchwartzMap ES ℂ) :
    Integrable (fun z : Space => ‖⇑s (euclidPoint z)‖ ^ 2) volume :=
  ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).2
    ((s.memLp 2 volume).integrable_norm_pow (by norm_num))

/-- **Crown-form finite energy of the free carrier at every `t ≥ 0`,**
conditional on exactly one named input: each physical coordinate
`physicalCoord (freeHeatTraj ν u₀ t) i` is (the function underlying) a
`SchwartzMap ES ℂ`.  Supplying that witness is a single Mathlib-level API
step: it needs `Function.HasTemperateGrowth` for the Gaussian multiplier
`fun ξ : ES => (Real.exp (-(ν * ‖ξ‖ ^ 2 * t) : ℝ) : ℂ)` so that
`SchwartzMap.smulLeftCLM`/`bilinLeftCLM` can multiply it into the Schwartz
datum slice `̂u₀ᵢ`, after which `FourierTransformInv` maps SchwartzMaps to
SchwartzMaps.  This rev carries neither half (measured by source grep of
`Analysis/Distribution/SchwartzSpace` and `SpecialFunctions/Gaussian`).
Given `hs`, the proof is mechanical: `L²`-integrability of each Schwartz
coordinate, Euclidean transport along `euclidPoint`, and the
`norm_sq_le_sum_sq` bridge. -/
theorem freeHeatPhysical_finiteEnergy_of_schwartz (ν : ℝ) (_hν : 0 ≤ ν) (t : ℝ) (_ht : 0 ≤ t)
    (u₀ : SchwartzVelocity)
    (hs : ∀ i : Fin 3, ∃ g : SchwartzMap ES ℂ,
      physicalCoord (freeHeatTraj ν u₀ t) i = ⇑g) :
    Integrable (fun z : Space => ‖physicalVelocity (freeHeatTraj ν u₀) t z‖ ^ 2) volume := by
  obtain ⟨g₀, hg₀⟩ := hs 0
  obtain ⟨g₁, hg₁⟩ := hs 1
  obtain ⟨g₂, hg₂⟩ := hs 2
  have hcoord (i : Fin 3) :
      Continuous (fun z : Space => physicalVelocity (freeHeatTraj ν u₀) t z i) := by
    obtain ⟨g, hg⟩ := hs i
    have hz : (fun z : Space => physicalVelocity (freeHeatTraj ν u₀) t z i) =
        fun z => (⇑g (euclidPoint z)).re := by
      funext z
      show (physicalCoord (freeHeatTraj ν u₀ t) i (euclidPoint z)).re = _
      rw [hg]
    rw [hz]
    exact Complex.continuous_re.comp (g.continuous.comp (PiLp.continuous_toLp 2 _))
  have hmeas : AEStronglyMeasurable
      (fun z : Space => ‖physicalVelocity (freeHeatTraj ν u₀) t z‖ ^ 2) volume :=
    ((continuous_pi hcoord).aestronglyMeasurable).norm.pow 2
  have key (i : Fin 3) (g : SchwartzMap ES ℂ)
      (hg : physicalCoord (freeHeatTraj ν u₀ t) i = ⇑g) (z : Space) :
      (physicalVelocity (freeHeatTraj ν u₀) t z i) ^ 2 ≤ ‖⇑g (euclidPoint z)‖ ^ 2 := by
    show ((physicalCoord (freeHeatTraj ν u₀ t) i (euclidPoint z)).re) ^ 2 ≤ _
    rw [hg]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm (K := ℂ) _) 2
  have h0 : Integrable (fun z : Space => ‖⇑g₀ (euclidPoint z)‖ ^ 2) volume :=
    integrable_euclid_sq g₀
  have h1 : Integrable (fun z : Space => ‖⇑g₁ (euclidPoint z)‖ ^ 2) volume :=
    integrable_euclid_sq g₁
  have h2 : Integrable (fun z : Space => ‖⇑g₂ (euclidPoint z)‖ ^ 2) volume :=
    integrable_euclid_sq g₂
  have hsum : Integrable (fun z : Space =>
      ‖⇑g₀ (euclidPoint z)‖ ^ 2 + ‖⇑g₁ (euclidPoint z)‖ ^ 2 + ‖⇑g₂ (euclidPoint z)‖ ^ 2)
      volume :=
    (h0.add h1).add h2
  refine hsum.mono' hmeas (ae_of_all volume fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine le_trans (norm_sq_le_sum_sq _) ?_
  rw [Fin.sum_univ_three (fun i => (physicalVelocity (freeHeatTraj ν u₀) t z i) ^ 2)]
  exact add_le_add (add_le_add (key 0 g₀ hg₀ z) (key 1 g₁ hg₁ z)) (key 2 g₂ hg₂ z)

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
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.freeHeatCoord_eq
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.norm_freeHeatCoord_le
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.integral_normSq_freeHeatCoord_le
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.sum_integral_normSq_freeHeat_le_initial
#print axioms Navier.Analysis.WholeSpaceCarrierReconstruction.freeHeatPhysical_finiteEnergy_of_schwartz
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceCarrierReconstruction.sum_integral_normSq_freeHeat_le_initial
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceCarrierReconstruction.freeHeatPhysical_finiteEnergy_of_schwartz
