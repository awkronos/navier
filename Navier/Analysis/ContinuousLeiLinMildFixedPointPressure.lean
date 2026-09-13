import Navier.Analysis.ContinuousLeiLinMildFixedPoint
import Navier.Analysis.ContinuousLeiLinPressureReconstruction
import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
import Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
import Navier.Analysis.ContinuousLeiLinActualPolarization
import Navier.Analysis.ContinuousLeiLinRecentTailInputs
import Navier.Analysis.ContinuousLeiLinPressurePhysical

/-!
# Pressure consumed by the mild fixed point

This module makes `continuousPressureFourier` a live consumer of the mild
fixed-point theorem `actual_existsUnique_mildFixedPoint`, honestly at the
repository's abstraction layer.

Five things are established here:

1. **Nonvacuity by concrete discharge.**  The `MildAssemblyLeaves` record is
   instantiated at the zero datum (`a = 0`, `R = 0`).  There the unique box
   element has both completed slot norms equal to `0`, so every representative
   section is almost everywhere zero at every time (the `RepresentativeGoodAt`
   norm clause kills the exceptional-time escape: a good time must satisfy
   `‖slot t‖ ≤ ‖slot‖ = 0`), hence the Navier source, the mild image, and the
   pressure are literally zero, and all twelve record fields close.  Feeding
   the instantiated record to `actual_existsUnique_mildFixedPoint` exhibits a
   nonvacuous mild fixed point (`existsUnique_mildFixedPoint_zeroBox`).
2. **Transported pressure budgets at a box element's representative.**
   `‖p̂(rep t)‖_{X¹} ≤ 2·(2R + X¹(rep t))·X¹(rep t)` and
   `‖∂ᵢp̂(rep t)‖_{X⁻¹} ≤ 2R · X¹(rep t)` pointwise in `t`, where `2R` is the
   box radius of the `X⁻¹` slot and the time-integrated `X¹` budget
   `∫ X¹(rep t) ≤ 2 ν⁻¹ R` is dug out of the box
   (`integral_coordinateX1Mass_rep_le`).
3. **Consumption identity.**  A fixed point of `actualMildSelfMap` has
   almost-everywhere-in-time pressure agreement: the pressure of its
   representative section equals the pressure of its own mild image
   (`fixedPoint_pressureEq`), bridged by
   `nested_ae_eq_of_toXm1TimeSlot_eq`.
4. **The Duhamel feed consumed at the fixed point.**  The feed theorem
   `normXm1_continuousPressureDuhamel_grad_le` is instantiated at the fixed
   point's representative section: at the zero box all four integrability
   leaves close (the integrands are literally zero) and the budget closes at
   `0` (`zeroBox_fixedPoint_pressureDuhamel_grad_normXm1_eq_zero`); for a
   general box the same chain is stated conditionally with the exact
   travelling premises named, ending at `4 ν⁻¹ R²`
   (`pressureDuhamel_grad_normXm1_le_of_feed`).
5. **The flagship physical pairing consumed at a box representative.**
   `continuousPressurePhysical_pairing_rep` instantiates the landed
   `ContinuousLeiLinPressurePhysical` flagship
   `continuousPressurePhysical_pairing_physicalLaplacian` at the everywhere
   raw representative section of a box element: its `AES`/`L¹` premises close
   from the box's weighted integrability via the coordinate `X⁰`
   interpolation proved here, so the physical-space Laplacian pairing becomes
   a live consumer of fixed-point-side data.

Truth checks performed by these statements: zero data (`a = 0`, `R = 0`)
degenerate to zero pressure and a zero budget (`zeroBox_*`, the `T = 0`
horizon is the null time measure so a.e.-in-time clauses are inert);
`x = y` polarization trivializes at the zero box because both representative
sections are a.e. zero (`zeroBox_diff_ae_zero`).

Deliberately NOT done here (named residuals):
- the general quotient-box instantiation of `MildAssemblyLeaves` (peer lane
  L6a, `ContinuousLeiLinMildAssemblyLeaves.lean`);
- the continuous-class non-degenerate discharge: the `hjoint*` matching lemmas
  below show the record's joint-measurability leaves are EXACTLY the outputs
  of `ContinuousLeiLinRecentTailInputs` suppliers, but their continuity
  hypotheses on quotient representatives are what no supplier can provide
  (noncanonical `L¹` selections);
- the spacetime feed hypotheses (`hb`, `hf`, `h0`) for non-zero boxes, which
  need joint measurability of `(ξ, s) ↦ p̂(rep s) ξ` — the zero-box instances
  close only because the integrands are literally zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal NNReal FourierTransform SchwartzMap
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinPressureReconstruction
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinRecentTailInputs
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinPressurePhysical
open Navier.Analysis.ComplexLerayNorm

namespace Navier.Analysis.ContinuousLeiLinMildFixedPointPressure

/-! ## Coordinate `X⁰` interpolation -/

private theorem eventually_norm_coord_le_weight_sum (u : ES → ComplexSpace) (i : Fin 3) :
    ∀ᵐ ξ ∂volume, ‖u ξ i‖ ≤ ‖ξ‖⁻¹ * ‖u ξ i‖ + ‖ξ‖ * ‖u ξ i‖ := by
  filter_upwards [show ∀ᵐ ξ : ES, ξ ≠ 0 by simp [ae_iff, measure_singleton]] with ξ hξ
  have h0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  by_cases hr : ‖ξ‖ ≤ 1
  · have hle : (1 : ℝ) ≤ ‖ξ‖⁻¹ := by rwa [one_le_inv₀ h0]
    have hstep : ‖u ξ i‖ ≤ ‖ξ‖⁻¹ * ‖u ξ i‖ := by
      simpa using mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    exact hstep.trans (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  · have hge : (1 : ℝ) ≤ ‖ξ‖ := le_of_lt (not_le.mp hr)
    have hstep : ‖u ξ i‖ ≤ ‖ξ‖ * ‖u ξ i‖ := by
      simpa using mul_le_mul_of_nonneg_right hge (norm_nonneg _)
    exact hstep.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _)))

/-- Finite-coordinate interpolation: coordinatewise `X⁻¹` and `X¹`
integrability, plus the measurability the carrier provides, force coordinatewise
`X⁰` integrability.  The majorant `‖ξ‖⁻¹‖u ξ i‖ + ‖ξ‖‖u ξ i‖` dominates
`‖u ξ i‖` on the unit ball and its complement separately; the zero frequency
is a null set. -/
theorem integrable_norm_continuousCoordinate_of_Xm1_X1
    (u : ES → ComplexSpace) (i : Fin 3)
    (huM : AEStronglyMeasurable (fun ξ : ES => u ξ i) volume)
    (huXm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (huX1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    Integrable (fun ξ : ES => ‖u ξ i‖) := by
  have hdom : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖ + ‖ξ‖ * ‖u ξ i‖) :=
    huXm1.add huX1
  refine hdom.mono' huM.norm ?_
  filter_upwards [eventually_norm_coord_le_weight_sum u i] with ξ hξ
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  simpa using hξ

/-- The aggregated coordinate `X⁰` budget of the interpolation. -/
theorem coordinateX0Mass_le_coordinateXm1Mass_add_coordinateX1Mass
    (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => u ξ i) volume)
    (hum1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hu1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    coordinateX0Mass u ≤ coordinateXm1Mass u + coordinateX1Mass u := by
  unfold coordinateX0Mass coordinateXm1Mass coordinateX1Mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  show (∫ ξ : ES, ‖u ξ i‖) ≤ normXm1 (fun ξ : ES => u ξ i) + normX1 (fun ξ : ES => u ξ i)
  unfold normXm1 normX1
  rw [← integral_add (hum1 i) (hu1 i)]
  refine integral_mono_ae (integrable_norm_continuousCoordinate_of_Xm1_X1 u i (huM i)
      (hum1 i) (hu1 i)) ((hum1 i).add (hu1 i)) ?_
  exact eventually_norm_coord_le_weight_sum u i

/-! ## Almost-everywhere invariance of the pressure reconstruction -/

/-- The pressure reconstruction is invariant under almost-everywhere changes
of the velocity profile: the symbol is built from `L¹` convolutions, and
`convolution_congr` transports a.e. equality. -/
theorem continuousPressureFourier_congr_ae (u v : ES → ComplexSpace)
    (h : u =ᵐ[volume] v) : continuousPressureFourier u = continuousPressureFourier v := by
  have hu : ∀ i : Fin 3, (fun η : ES => u η i) =ᵐ[volume] fun η : ES => v η i := by
    intro i; exact h.mono fun ξ hξ => congrFun hξ i
  have hconv : ∀ i j : Fin 3,
      ((fun η : ES => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => u η j)) =
        ((fun η : ES => v η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => v η j)) :=
    fun i j => convolution_congr (ContinuousLinearMap.mul ℂ ℂ) (hu i) (hu j)
  funext ξ
  have hsum : (fun i : Fin 3 => ∑ j : Fin 3, (pressureSymbol ξ i j : ℂ) *
        ((fun η : ES => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => u η j)) ξ) =
      (fun i : Fin 3 => ∑ j : Fin 3, (pressureSymbol ξ i j : ℂ) *
        ((fun η : ES => v η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => v η j)) ξ) := by
    funext i
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z : ℂ => (pressureSymbol ξ i j : ℂ) * z) (congrFun (hconv i j) ξ)
  unfold continuousPressureFourier
  rw [hsum]

/-! ## The zero-box cascade -/

private theorem hac_volume_xm1 (ν : ℝ≥0) (hν : 0 < ν) :
    volume ≪ xm1FrequencyMeasure :=
  (volume_absolutelyContinuous_commonFrequencyMeasure ν hν).trans
    (Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_xm1 ν))

private abbrev zeroBox (ν : ℝ≥0) (T : ℝ) :=
  ActualLinkedBox ν T (2 * (0 : ℝ)) (2 * (0 : ℝ))

/-- Both completed slots of the zero-radius linked box vanish: the box
property forces the slot norms below `2 · 0 = 0`. -/
theorem zeroBox_slots_eq_zero (ν : ℝ≥0) (T : ℝ)
    (x : zeroBox ν T) :
    (x.1.1.fst : Xm1TimeSlot T) = 0 ∧ (x.1.1.snd : ViscousX1TimeSlot ν T) = 0 := by
  refine ⟨norm_le_zero_iff.mp (x.property.1.trans (le_of_eq (mul_zero 2))),
    norm_le_zero_iff.mp (x.property.2.trans (le_of_eq (mul_zero 2)))⟩

/-- **The zero-box cascade.**  At the zero box the everywhere representative
of the unique box element is almost everywhere zero at EVERY time.  A good
time has slot value `0` because the `RepresentativeGoodAt` norm clause forces
`‖slot t‖ ≤ ‖slot‖ = 0`; the `a.e.` identity then transfers through
`volume ≪ xm1FrequencyMeasure`.  A bad time is literally `0`. -/
theorem zeroBox_rep_ae_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) :
    everywhereRawRepresentative ν T x.1 t =ᵐ[volume] 0 := by
  have hslot : (x.1.1.fst : Xm1TimeSlot T) = 0 := (zeroBox_slots_eq_zero ν T x).1
  by_cases ht : RepresentativeGoodAt ν T x.1 t
  · have hrep : everywhereRawRepresentative ν T x.1 t =
        xm1RawRepresentative ν T x.1 t := by
      simp [everywhereRawRepresentative, ht]
    rw [hrep]
    have ht0 : ((x.1.1.fst : Xm1TimeSlot T) t : Xm1Spatial) = 0 := by
      refine norm_le_zero_iff.mp ?_
      calc ‖(x.1.1.fst : Xm1TimeSlot T) t‖ ≤ ‖(x.1.1.fst : Xm1TimeSlot T)‖ := ht.2.2
        _ = 0 := by rw [hslot]; exact norm_zero
    have hraw : xm1RawRepresentative ν T x.1 t =ᵐ[xm1FrequencyMeasure] 0 := by
      have hz : (⇑((x.1.1.fst : Xm1TimeSlot T) t) : ES → FourierCoordinateL1) =ᵐ[xm1FrequencyMeasure]
          0 := by
        rw [ht0]
        exact Lp.coeFn_zero FourierCoordinateL1 1 xm1FrequencyMeasure
      filter_upwards [hz] with ξ hξ
      simp [xm1RawRepresentative, hξ]
    exact (hac_volume_xm1 ν hν).ae_eq hraw
  · simp [everywhereRawRepresentative, ht]

/-- The difference of two zero-box representatives is a.e. zero: the
`x = y` polarization edge degenerates correctly. -/
theorem zeroBox_diff_ae_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : zeroBox ν T) (t : ℝ) :
    commonRepresentativeDifference ν T x.1 y.1 t =ᵐ[volume] 0 := by
  unfold commonRepresentativeDifference
  filter_upwards [zeroBox_rep_ae_zero ν hν T x t, zeroBox_rep_ae_zero ν hν T y t]
    with ξ hξ hyξ
  rw [hξ, hyξ]
  simp

private theorem continuousNavierBilinear_congr_zero (u v : ES → ComplexSpace)
    (hu : u =ᵐ[volume] 0) (hv : v =ᵐ[volume] 0) :
    continuousNavierBilinear u v = 0 := by
  refine (continuousNavierBilinear_congr_ae u 0 v 0 hu hv).trans ?_
  funext ξ
  show continuousLeray ξ (Complex.I •
      rawNavierConvection (0 : ES → ComplexSpace) (0 : ES → ComplexSpace) ξ) = 0
  have hraw : rawNavierConvection (0 : ES → ComplexSpace) (0 : ES → ComplexSpace) ξ = 0 := by
    ext i
    simp only [rawNavierConvection]
    refine Finset.sum_eq_zero fun j _ => mul_eq_zero.2 (Or.inr ?_)
    have hc : ((fun η : ES => (0 : ES → ComplexSpace) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        fun η : ES => (0 : ES → ComplexSpace) η i) = 0 := zero_convolution
    rw [hc]
    simp
  rw [hraw]
  simp [continuousLeray]

/-- The Navier source of any zero-box representative pair vanishes literally. -/
theorem zeroBox_source_eq_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (s : ℝ) :
    continuousNavierSource (everywhereRawRepresentative ν T x.1)
      (everywhereRawRepresentative ν T x.1) s = 0 := by
  unfold continuousNavierSource
  exact continuousNavierBilinear_congr_zero _ _
    (zeroBox_rep_ae_zero ν hν T x s) (zeroBox_rep_ae_zero ν hν T x s)

/-- **Degenerate-data truth check.**  The zero-box representative section
reconstructs the zero pressure density at every time. -/
theorem zeroBox_pressure_eq_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) :
    continuousPressureFourier (everywhereRawRepresentative ν T x.1 t) = 0 := by
  refine (continuousPressureFourier_congr_ae _ _ (zeroBox_rep_ae_zero ν hν T x t)).trans
    continuousPressureFourier_zero_velocity

/-- The pressure source of the zero-box representative field vanishes. -/
theorem zeroBox_pressSource_eq_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (s : ℝ) :
    continuousPressureSource (everywhereRawRepresentative ν T x.1) s = 0 := by
  unfold continuousPressureSource
  exact zeroBox_pressure_eq_zero ν hν T x s

private theorem continuousDuhamel_eq_zero_of_source_zero
    (u v : ℝ → ES → ComplexSpace) (ν t : ℝ)
    (h : ∀ s, continuousNavierSource u v s = 0) : continuousDuhamel ν u v t = 0 := by
  funext ξ i
  show ∫ s in Icc (0 : ℝ) t, heatMode ν (t - s)
      (fun ζ : ES => continuousNavierSource u v s ζ i) ξ = 0
  have hfun : (fun s : ℝ => heatMode ν (t - s)
      (fun ζ : ES => continuousNavierSource u v s ζ i) ξ) = fun _ => 0 := by
    funext s
    rw [h s]
    simp [heatMode]
  rw [hfun]
  simp

/-- The Duhamel integral of the zero-box self-source vanishes. -/
theorem zeroBox_duhamel_eq_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) :
    continuousDuhamel (ν : ℝ) (everywhereRawRepresentative ν T x.1)
      (everywhereRawRepresentative ν T x.1) t = 0 :=
  continuousDuhamel_eq_zero_of_source_zero _ _ (ν : ℝ) t
    fun s => zeroBox_source_eq_zero ν hν T x s

/-- The mild image of the zero datum driven by the zero-box representative
vanishes at every point. -/
theorem zeroBox_mildImage_eq_zero (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) (ξ : ES) :
    mildImage ν hν (0 : ES → ComplexSpace) (everywhereRawRepresentative ν T x.1) t ξ = 0 := by
  set u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1 with hu_def
  unfold mildImage ContinuousLeiLinSelfMap.continuousMildImage
  have h1 : heatVec (ν : ℝ) t (0 : ES → ComplexSpace) ξ = 0 := by
    ext i
    simp [heatVec, heatMode]
  have h2 : continuousDuhamel (ν : ℝ) u u t ξ = 0 := by
    rw [zeroBox_duhamel_eq_zero ν hν T x t]
    simp
  rw [h1, h2]
  simp

private theorem zeroBox_mildImage_fn (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) :
    mildImage ν hν (0 : ES → ComplexSpace) (everywhereRawRepresentative ν T x.1) =
      fun _ => (0 : ES → ComplexSpace) := by
  funext t
  funext ξ
  exact zeroBox_mildImage_eq_zero ν hν T x t ξ

private theorem zeroBox_mildImage_at (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) :
    mildImage ν hν (0 : ES → ComplexSpace) (everywhereRawRepresentative ν T x.1) t = 0 :=
  congrFun (zeroBox_mildImage_fn ν hν T x) t

private theorem coordinateX1Mass_nonneg (u : ES → ComplexSpace) :
    0 ≤ coordinateX1Mass u := by
  unfold coordinateX1Mass
  refine Finset.sum_nonneg fun i _ => ?_
  unfold normX1
  exact integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem normXm1_nonneg (f : ES → ℂ) : 0 ≤ normXm1 f := by
  unfold normXm1
  exact integral_nonneg fun ξ =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)

private theorem coordinateX0Mass_eq_zero_of_ae (w : ES → ComplexSpace)
    (hw : w =ᵐ[volume] 0) : coordinateX0Mass w = 0 := by
  unfold coordinateX0Mass
  apply Finset.sum_eq_zero
  intro i _
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards [hw] with ξ hξ
  simp [hξ]

private theorem xm1Section_zero (w : ℝ → ES → ComplexSpace)
    (hw : ∀ t, w t = (0 : ES → ComplexSpace))
    (hM : ∀ t i, AEStronglyMeasurable (fun ξ : ES => w t ξ i) volume)
    (hI : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w t ξ i‖)) :
    xm1Section w hM hI = fun _ => 0 := by
  funext t
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have h : ⇑(xm1Section w hM hI t) =ᵐ[xm1FrequencyMeasure] coordinateL1 (w t) :=
    coeFn_toXm1Spatial (w t) (hM t) (hI t)
  rw [hw t] at h
  have hz : coordinateL1 (0 : ES → ComplexSpace) = fun _ => (0 : FourierCoordinateL1) := by
    funext ξ
    simp [coordinateL1]
  rw [hz] at h
  exact h

private theorem viscousX1Section_zero (w : ℝ → ES → ComplexSpace) (ν : ℝ≥0)
    (hw : ∀ t, w t = (0 : ES → ComplexSpace))
    (hM : ∀ t i, AEStronglyMeasurable (fun ξ : ES => w t ξ i) volume)
    (hI : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖w t ξ i‖)) :
    viscousX1Section w hM hI ν = fun _ => 0 := by
  funext t
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have h : ⇑(viscousX1Section w hM hI ν t) =ᵐ[viscousX1FrequencyMeasure ν]
      coordinateL1 (w t) := coeFn_toViscousX1Spatial ν (w t) (hM t) (hI t)
  rw [hw t] at h
  have hz : coordinateL1 (0 : ES → ComplexSpace) = fun _ => (0 : FourierCoordinateL1) := by
    funext ξ
    simp [coordinateL1]
  rw [hz] at h
  exact h

private theorem zeroBox_hmM (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES =>
        mildImage ν hν (0 : ES → ComplexSpace)
          (everywhereRawRepresentative ν T x.1) t ξ i) volume := by
  have hfn : (fun ξ : ES => mildImage ν hν (0 : ES → ComplexSpace)
      (everywhereRawRepresentative ν T x.1) t ξ i) = fun _ => (0 : ℂ) := by
    funext ξ
    rw [zeroBox_mildImage_eq_zero ν hν T x t ξ]
    simp
  rw [hfn]
  exact aestronglyMeasurable_const

private theorem zeroBox_hmXm1 (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildImage ν hν (0 : ES → ComplexSpace)
        (everywhereRawRepresentative ν T x.1) t ξ i‖) := by
  have hfn : (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildImage ν hν (0 : ES → ComplexSpace)
      (everywhereRawRepresentative ν T x.1) t ξ i‖) = fun _ => (0 : ℝ) := by
    funext ξ
    rw [zeroBox_mildImage_eq_zero ν hν T x t ξ]
    simp
  rw [hfn]
  simp

private theorem zeroBox_hmX1 (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖mildImage ν hν (0 : ES → ComplexSpace)
        (everywhereRawRepresentative ν T x.1) t ξ i‖) := by
  have hfn : (fun ξ : ES => ‖ξ‖ * ‖mildImage ν hν (0 : ES → ComplexSpace)
      (everywhereRawRepresentative ν T x.1) t ξ i‖) = fun _ => (0 : ℝ) := by
    funext ξ
    rw [zeroBox_mildImage_eq_zero ν hν T x t ξ]
    simp
  rw [hfn]
  simp

/-! ## The assembly record at the zero box: nonvacuity -/

/-- **The concrete discharge of `MildAssemblyLeaves`.**  At the zero datum and
zero radius all twelve leaves close: every quantified function is literally
zero, so the joint measurabilities are `aestronglyMeasurable_const`, the
integrabilities are `integrable_zero`, and the polarization leaves are
`0 ≤ 0 + 0`.  This is the non-degenerate input the fixed-point theorem needs
to produce a fixed point. -/
theorem record_zeroBox (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) :
    MildAssemblyLeaves ν hν T 0 hT (0 : ES → ComplexSpace)
      (fun i => by simpa using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume))
      (fun i => by simp)
      (fun i => by simp)
      (by simp [coordinateXm1Mass, normXm1]) :=
  { hRν := by positivity
    hjointDiag := fun x => by
      have hf : (fun p : ES × ℝ => complexEuclideanPoint (continuousNavierSource
            (everywhereRawRepresentative ν T x.1)
            (everywhereRawRepresentative ν T x.1) p.2 p.1)) =
          fun _ => complexEuclideanPoint (0 : ComplexSpace) := by
        funext p
        rw [zeroBox_source_eq_zero ν hν T x p.2]
        simp
      rw [hf]
      exact aestronglyMeasurable_const
    hmM := fun x t i => zeroBox_hmM ν hν T x t i
    hmXm1 := fun x t i => zeroBox_hmXm1 ν hν T x t i
    hmX1 := fun x t i => zeroBox_hmX1 ν hν T x t i
    hmXm1Time := fun x => by
      have hw : ∀ t, mildImage ν hν (0 : ES → ComplexSpace)
          (everywhereRawRepresentative ν T x.1) t = (0 : ES → ComplexSpace) :=
        fun t => congrFun (zeroBox_mildImage_fn ν hν T x) t
      have hzero := xm1Section_zero
        (mildImage ν hν (0 : ES → ComplexSpace) (everywhereRawRepresentative ν T x.1)) hw
        (zeroBox_hmM ν hν T x) (zeroBox_hmXm1 ν hν T x)
      rw [hzero]
      exact aestronglyMeasurable_const
    hmX1Time := fun x => by
      have hw : ∀ t, mildImage ν hν (0 : ES → ComplexSpace)
          (everywhereRawRepresentative ν T x.1) t = (0 : ES → ComplexSpace) :=
        fun t => congrFun (zeroBox_mildImage_fn ν hν T x) t
      have hzero := viscousX1Section_zero
        (mildImage ν hν (0 : ES → ComplexSpace) (everywhereRawRepresentative ν T x.1)) ν hw
        (zeroBox_hmM ν hν T x) (zeroBox_hmX1 ν hν T x)
      rw [hzero]
      exact aestronglyMeasurable_const
    hmX1Int := fun x => by
      have hf : (fun t : ℝ => coordinateX1Mass (mildImage ν hν (0 : ES → ComplexSpace)
          (everywhereRawRepresentative ν T x.1) t)) = fun _ => (0 : ℝ) := by
        funext t
        rw [zeroBox_mildImage_at ν hν T x t]
        simp [coordinateX1Mass, normX1]
      rw [hf]
      exact integrable_const 0
    hjointL := fun x y => by
      have hdiff (s : ℝ) : commonRepresentativeDifference ν T x.1 y.1 s =ᵐ[volume] 0 :=
        zeroBox_diff_ae_zero ν hν T x y s
      have hf : (fun p : ES × ℝ => complexEuclideanPoint (continuousNavierSource
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) p.2 p.1)) =
          fun _ => complexEuclideanPoint (0 : ComplexSpace) := by
        funext p
        have hsrc : continuousNavierSource (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) p.2 = 0 := by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _ (hdiff p.2)
            (zeroBox_rep_ae_zero ν hν T x p.2)
        rw [hsrc]
        simp
      rw [hf]
      exact aestronglyMeasurable_const
    hjointR := fun x y => by
      have hdiff (s : ℝ) : commonRepresentativeDifference ν T x.1 y.1 s =ᵐ[volume] 0 :=
        zeroBox_diff_ae_zero ν hν T x y s
      have hf : (fun p : ES × ℝ => complexEuclideanPoint (continuousNavierSource
            (everywhereRawRepresentative ν T y.1)
            (commonRepresentativeDifference ν T x.1 y.1) p.2 p.1)) =
          fun _ => complexEuclideanPoint (0 : ComplexSpace) := by
        funext p
        have hsrc : continuousNavierSource (everywhereRawRepresentative ν T y.1)
            (commonRepresentativeDifference ν T x.1 y.1) p.2 = 0 := by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _
            (zeroBox_rep_ae_zero ν hν T y p.2) (hdiff p.2)
        rw [hsrc]
        simp
      rw [hf]
      exact aestronglyMeasurable_const
    hXmDiff := fun x y => by
      refine ae_of_all _ fun t => ?_
      have hA : (fun ξ : ES => mildImage ν hν (0 : ES → ComplexSpace)
            (everywhereRawRepresentative ν T x.1) t ξ -
            mildImage ν hν (0 : ES → ComplexSpace)
              (everywhereRawRepresentative ν T y.1) t ξ) =
          fun _ => (0 : ComplexSpace) := by
        funext ξ
        rw [zeroBox_mildImage_eq_zero ν hν T x t ξ, zeroBox_mildImage_eq_zero ν hν T y t ξ]
        simp
      have hdL : continuousDuhamel (ν : ℝ) (commonRepresentativeDifference ν T x.1 y.1)
          (everywhereRawRepresentative ν T x.1) t = 0 :=
        continuousDuhamel_eq_zero_of_source_zero _ _ (ν : ℝ) t fun s => by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _
            (zeroBox_diff_ae_zero ν hν T x y s) (zeroBox_rep_ae_zero ν hν T x s)
      have hdR : continuousDuhamel (ν : ℝ) (everywhereRawRepresentative ν T y.1)
          (commonRepresentativeDifference ν T x.1 y.1) t = 0 :=
        continuousDuhamel_eq_zero_of_source_zero _ _ (ν : ℝ) t fun s => by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _
            (zeroBox_rep_ae_zero ν hν T y s) (zeroBox_diff_ae_zero ν hν T x y s)
      rw [hA, hdL, hdR]
      simp [coordinateXm1Mass, normXm1]
    hX1Diff := fun x y => by
      have hA : (fun t : ℝ => coordinateX1Mass (fun ξ : ES =>
            mildImage ν hν (0 : ES → ComplexSpace)
              (everywhereRawRepresentative ν T x.1) t ξ -
              mildImage ν hν (0 : ES → ComplexSpace)
                (everywhereRawRepresentative ν T y.1) t ξ)) = fun _ => (0 : ℝ) := by
        funext t
        have key : (fun ξ : ES => mildImage ν hν (0 : ES → ComplexSpace)
              (everywhereRawRepresentative ν T x.1) t ξ -
              mildImage ν hν (0 : ES → ComplexSpace)
                (everywhereRawRepresentative ν T y.1) t ξ) =
            fun _ => (0 : ComplexSpace) := by
          funext ξ
          rw [zeroBox_mildImage_eq_zero ν hν T x t ξ, zeroBox_mildImage_eq_zero ν hν T y t ξ]
          simp
        rw [key]
        simp [coordinateX1Mass, normX1]
      have hR1 : (fun t : ℝ => coordinateX1Mass (continuousDuhamel (ν : ℝ)
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) t)) = fun _ => (0 : ℝ) := by
        funext t
        rw [continuousDuhamel_eq_zero_of_source_zero _ _ (ν : ℝ) t fun s => by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _
            (zeroBox_diff_ae_zero ν hν T x y s) (zeroBox_rep_ae_zero ν hν T x s)]
        simp [coordinateX1Mass, normX1]
      have hR2 : (fun t : ℝ => coordinateX1Mass (continuousDuhamel (ν : ℝ)
            (everywhereRawRepresentative ν T y.1)
            (commonRepresentativeDifference ν T x.1 y.1) t)) = fun _ => (0 : ℝ) := by
        funext t
        rw [continuousDuhamel_eq_zero_of_source_zero _ _ (ν : ℝ) t fun s => by
          unfold continuousNavierSource
          exact continuousNavierBilinear_congr_zero _ _
            (zeroBox_rep_ae_zero ν hν T y s) (zeroBox_diff_ae_zero ν hν T x y s)]
        simp [coordinateX1Mass, normX1]
      rw [hA, hR1, hR2]
      simp }

/-- **The mild fixed point exists and is unique — the nonvacuity witness.**
Feeding `record_zeroBox` to `actual_existsUnique_mildFixedPoint` fires the
theorem on a concrete box: there is a (necessarily unique) element of the
completed zero box fixed by the lifted mild image. -/
theorem existsUnique_mildFixedPoint_zeroBox (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) :
    ∃ x : ActualLinkedBox ν T (2 * (0 : ℝ)) (2 * (0 : ℝ)),
      actualMildSelfMap ν hν T (0 : ℝ) hT (0 : ES → ComplexSpace)
        (fun i => by simpa using (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume))
        (fun i => by simp)
        (fun i => by simp)
        (by simp [coordinateXm1Mass, normXm1])
        (record_zeroBox ν hν T hT) x = x ∧
        ∀ y : ActualLinkedBox ν T (2 * (0 : ℝ)) (2 * (0 : ℝ)),
          actualMildSelfMap ν hν T (0 : ℝ) hT (0 : ES → ComplexSpace)
            (fun i => by simpa using (aestronglyMeasurable_const :
              AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume))
            (fun i => by simp)
            (fun i => by simp)
            (by simp [coordinateXm1Mass, normXm1])
            (record_zeroBox ν hν T hT) y = y → y = x :=
  actual_existsUnique_mildFixedPoint ν hν T (0 : ℝ) hT (0 : ES → ComplexSpace)
    (fun i => by simpa using (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume))
    (fun i => by simp)
    (fun i => by simp)
    (by simp [coordinateXm1Mass, normXm1]) (record_zeroBox ν hν T hT)

/-! ## Continuous-class matching for the joint leaves (complementary evidence)

The record's three joint-measurability leaves are *exactly* the conclusions of
`ContinuousLeiLinRecentTailInputs`' suppliers at `τ = 0, t = T`, once the
representative sections are jointly coordinate-continuous.  These matching
lemmas show the record's reach: a continuous-class discharge would supply
`hjointDiag/hjointL/hjointR` verbatim.  The named residual is the continuity
hypothesis itself — quotient representatives are noncanonical `L¹`
selections, and no supplier proves their pointwise continuity (that is the
general quotient-box construction owned by lane L6a). -/

/-- `hjointDiag` matching: the continuous supplier produces the exact record
body `(rep x, rep x)` over the full horizon. -/
theorem hjointDiag_matching_of_continuous (ν : ℝ≥0) (T : ℝ)
    (x : ActualLinkedCarrier ν T)
    (hx : ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        everywhereRawRepresentative ν T x p.2 p.1 j)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T x)
          (everywhereRawRepresentative ν T x) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    (everywhereRawRepresentative ν T x) (everywhereRawRepresentative ν T x) 0 T hx hx

/-- `hjointL` matching: the continuous supplier produces the exact record
body `(rep x − rep y, rep x)`. -/
theorem hjointL_matching (ν : ℝ≥0) (T : ℝ) (x y : ActualLinkedCarrier ν T)
    (hd : ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        commonRepresentativeDifference ν T x y p.2 p.1 j))
    (hx : ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        everywhereRawRepresentative ν T x p.2 p.1 j)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (commonRepresentativeDifference ν T x y)
          (everywhereRawRepresentative ν T x) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    (commonRepresentativeDifference ν T x y) (everywhereRawRepresentative ν T x) 0 T hd hx

/-- `hjointR` matching: the continuous supplier produces the exact record
body `(rep y, rep x − rep y)`. -/
theorem hjointR_matching (ν : ℝ≥0) (T : ℝ) (x y : ActualLinkedCarrier ν T)
    (hy : ∀ i : Fin 3, Continuous (fun p : ES × ℝ =>
        everywhereRawRepresentative ν T y p.2 p.1 i))
    (hd : ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        commonRepresentativeDifference ν T x y p.2 p.1 j)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T y)
          (commonRepresentativeDifference ν T x y) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    (everywhereRawRepresentative ν T y) (commonRepresentativeDifference ν T x y) 0 T hy hd

/-! ## Transported pressure budgets at a box element's representative -/

/-- The `X¹` budget of the pressure of a box element's representative
section, with the `X⁰` factor replaced by the interpolated
`2 R + X¹(rep t)` bound transported from the box:
`‖p̂(rep t)‖_{X¹} ≤ 2 · (2R + X¹(rep t)) · X¹(rep t)`.  The bare `2 · X⁰ · X¹`
form is `normX1_continuousPressureFourier_le`; this is its box-transported
companion. -/
theorem normX1_continuousPressureFourier_rep_le (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) (t : ℝ) :
    normX1 (continuousPressureFourier (everywhereRawRepresentative ν T x.1 t)) ≤
      2 * (2 * R + coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)) *
        coordinateX1Mass (everywhereRawRepresentative ν T x.1 t) := by
  set u : ES → ComplexSpace := everywhereRawRepresentative ν T x.1 t with hu
  have hX1nn : 0 ≤ coordinateX1Mass u := coordinateX1Mass_nonneg u
  have hXm1 : coordinateXm1Mass u ≤ 2 * R :=
    (coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t).trans x.property.1
  have hX0 : coordinateX0Mass u ≤ coordinateXm1Mass u + coordinateX1Mass u :=
    coordinateX0Mass_le_coordinateXm1Mass_add_coordinateX1Mass u
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 t)
      (everywhereRawRepresentative_x1_integrable ν T x.1 t)
  have hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖) := fun j =>
    integrable_norm_continuousCoordinate_of_Xm1_X1 u j
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t j)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 t j)
      (everywhereRawRepresentative_x1_integrable ν T x.1 t j)
  calc normX1 (continuousPressureFourier u)
      ≤ 2 * coordinateX0Mass u * coordinateX1Mass u :=
        normX1_continuousPressureFourier_le u
          (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t) hu0
          (everywhereRawRepresentative_x1_integrable ν T x.1 t)
    _ ≤ 2 * (coordinateXm1Mass u + coordinateX1Mass u) * coordinateX1Mass u := by gcongr
    _ ≤ 2 * (2 * R + coordinateX1Mass u) * coordinateX1Mass u := by gcongr

/-- The honest `X⁻¹`-gradient form: `‖∂ᵢp̂(rep t)‖_{X⁻¹} ≤ 2R · X¹(rep t)`,
the fixed-time gradient budget composed with the coordinate Cauchy--Schwarz
interpolation and the box radius. -/
theorem normXm1_continuousPressureGrad_rep_le (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) (t : ℝ) (i : Fin 3) :
    normXm1 (fun ξ : ES => continuousPressureGrad (everywhereRawRepresentative ν T x.1 t) ξ i) ≤
      2 * R * coordinateX1Mass (everywhereRawRepresentative ν T x.1 t) := by
  set u : ES → ComplexSpace := everywhereRawRepresentative ν T x.1 t with hu
  have hX1nn : 0 ≤ coordinateX1Mass u := coordinateX1Mass_nonneg u
  have hXm1 : coordinateXm1Mass u ≤ 2 * R :=
    (coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t).trans x.property.1
  have hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖) := fun j =>
    integrable_norm_continuousCoordinate_of_Xm1_X1 u j
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t j)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 t j)
      (everywhereRawRepresentative_x1_integrable ν T x.1 t j)
  calc normXm1 (fun ξ : ES => continuousPressureGrad u ξ i)
      ≤ coordinateX0Mass u ^ 2 :=
        normXm1_continuousPressureGrad_le u i
          (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t) hu0
    _ ≤ coordinateXm1Mass u * coordinateX1Mass u :=
        coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass u
          (everywhereRawRepresentative_xm1_integrable ν T x.1 t)
          (everywhereRawRepresentative_x1_integrable ν T x.1 t)
    _ ≤ 2 * R * coordinateX1Mass u := mul_le_mul_of_nonneg_right hXm1 hX1nn

/-- The time-integrated `X¹` budget of a box element's representative section,
dug out of the viscous slot: `∫ X¹(rep t) ≤ 2 ν⁻¹ R`. -/
theorem integral_coordinateX1Mass_rep_le (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∫ t, coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)
        ∂(leiLinTimeMeasure T)) ≤
      2 * (ν : ℝ)⁻¹ * R := by
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hsec : (∫ t, coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)
        ∂(leiLinTimeMeasure T)) =
      (ν : ℝ)⁻¹ * ∫ t, ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T) := by
    have hnorm : ∀ s : ℝ, ‖everywhereViscousX1Section ν hν T x.1 s‖ =
        (ν : ℝ) * coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) :=
      fun s => norm_viscousX1Section (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
        (everywhereRawRepresentative_x1_integrable ν T x.1) ν s
    have hfun : (fun t : ℝ => coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)) =
        fun t => (ν : ℝ)⁻¹ * ‖everywhereViscousX1Section ν hν T x.1 t‖ := by
      funext t
      rw [hnorm t, ← mul_assoc, inv_mul_cancel₀ hνR.ne', one_mul]
    have hpull : ∫ t, (ν : ℝ)⁻¹ * ‖everywhereViscousX1Section ν hν T x.1 t‖
        ∂(leiLinTimeMeasure T) =
        (ν : ℝ)⁻¹ * ∫ t, ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T) := by
      show ∫ t, (ν : ℝ)⁻¹ • ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T) =
          (ν : ℝ)⁻¹ • ∫ t, ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T)
      exact integral_smul _ _
    rw [hfun, hpull]
  have hint : (∫ t, ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T)) =
      ‖(x.1.1.snd : ViscousX1TimeSlot ν T)‖ := by
    have hc : (∫ t, ‖everywhereViscousX1Section ν hν T x.1 t‖ ∂(leiLinTimeMeasure T)) =
        ∫ t, ‖((x.1.1.snd : ViscousX1TimeSlot ν T) t)‖ ∂(leiLinTimeMeasure T) :=
      integral_congr_ae
        ((everywhereViscousX1Section_eq_ae ν hν T x.1).mono fun t ht => congrArg Norm.norm ht)
    exact hc.trans ((L1.norm_eq_integral_norm (x.1.1.snd : ViscousX1TimeSlot ν T)).symm)
  rw [hsec, hint]
  refine (mul_le_mul_of_nonneg_left x.property.2 (inv_nonneg.mpr hνR.le)).trans ?_
  exact le_of_eq (by ring)

/-! ## The consumption identities -/

/-- **The fixed point's pressure identity.**  If the lifted mild image fixes
the box element `x`, then for almost every time the pressure of its
representative section equals the pressure of its own mild image.  The bridge
is `nested_ae_eq_of_toXm1TimeSlot_eq`: equality of the fixed point's outer
`X⁻¹` slot with the slot rebuilt from the mild image forces a.e.-in-time
equality of the underlying frequency fields, and the pressure reconstruction
is a.e.-invariant (`continuousPressureFourier_congr_ae`).  This declaration
states neither the self-map nor the pressure budget alone: it needs the
fixed-point hypothesis and the pressure module together. -/
theorem fixedPoint_pressureEq (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      continuousPressureFourier (everywhereRawRepresentative ν T x.1 t) =
        continuousPressureFourier
          (mildImage ν hν a (everywhereRawRepresentative ν T x.1) t) := by
  set u : ℝ → ES → ComplexSpace :=
    mildImage ν hν a (everywhereRawRepresentative ν T x.1) with hu_def
  obtain ⟨hb1, _⟩ := selfMapEstimate ν hν T R hT a haM ha ha1 haR L x
  have hval : (actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x).1 = x.1 :=
    congrArg Subtype.val hx
  have h0 : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst = x.1.1.fst :=
    congrArg (fun c : ActualLinkedCarrier ν T => c.1.fst) hval
  have hkey : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst =
      toXm1TimeSlot u (L.hmM x) (L.hmXm1 x) T (2 * R) (L.hmXm1Time x) hb1 := rfl
  have hevery : everywhereXm1TimeSlot ν hν T x.1 =
      toXm1TimeSlot (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
        (everywhereRawRepresentative_xm1_integrable ν T x.1) T
        ‖(x.1.1.fst : Xm1TimeSlot T)‖
        (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
        (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) := rfl
  have hslot : toXm1TimeSlot u (L.hmM x) (L.hmXm1 x) T (2 * R) (L.hmXm1Time x) hb1 =
      toXm1TimeSlot (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
        (everywhereRawRepresentative_xm1_integrable ν T x.1) T
        ‖(x.1.1.fst : Xm1TimeSlot T)‖
        (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
        (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) := by
    rw [← hkey, h0, ← hevery]
    exact (everywhereXm1TimeSlot_eq ν hν T x.1).symm
  have hae := nested_ae_eq_of_toXm1TimeSlot_eq ν hν T (2 * R) ‖(x.1.1.fst : Xm1TimeSlot T)‖
    u (everywhereRawRepresentative ν T x.1)
    (L.hmM x) (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
    (L.hmXm1 x) (everywhereRawRepresentative_xm1_integrable ν T x.1)
    (L.hmXm1Time x) (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
    hb1 (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) hslot
  filter_upwards [hae] with t ht
  exact continuousPressureFourier_congr_ae
    (u := everywhereRawRepresentative ν T x.1 t) (h := ht.symm)

private theorem integrable_pressureDuhamel_coord (w : ES → ComplexSpace) (i : Fin 3)
    (hw : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => w η j) volume)
    (hw0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖w η j‖)) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureFourier w ξ‖) := by
  have hsum : Integrable (fun ξ : ES => ∑ j : Fin 3, ∑ k : Fin 3,
      convolution (fun η : ES => ‖w η j‖) (fun η : ES => ‖w η k‖) ξ) :=
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun k _ =>
        integrable_scalar_convolution _ _ (hw0 j) (hw0 k)
  have hmeas : AEStronglyMeasurable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureFourier w ξ‖) := by
    have hc : AEStronglyMeasurable (fun ξ : ES => (ξ i : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)).aestronglyMeasurable
    have h1 : AEStronglyMeasurable (fun ξ : ES => ‖continuousPressureGrad w ξ i‖) :=
      ((hc.mul (aesstronglyMeasurable_continuousPressureFourier w hw hw0)).norm.congr
        (by filter_upwards with ξ; simp only [continuousPressureGrad_apply, Pi.mul_apply]))
    have h2 : (fun ξ : ES => ‖(ξ i : ℂ) • continuousPressureFourier w ξ‖) =
        fun ξ : ES => ‖continuousPressureGrad w ξ i‖ := by
      funext ξ; simp only [continuousPressureGrad_apply, smul_eq_mul]
    have h3 : (fun ξ : ES => ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureFourier w ξ‖) =
        (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousPressureGrad w ξ i‖) := by
      funext ξ
      rw [congrFun h2 ξ]
    rw [h3]
    refine (continuous_norm.aestronglyMeasurable.inv₀).mul h1
  refine hsum.mono' hmeas ?_
  filter_upwards with ξ
  rw [smul_eq_mul, ← continuousPressureGrad_apply,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
  exact normXm1_continuousPressureGrad_pointwise w ξ i

/-- **The feed consumed at the zero-box fixed point.**  The Duhamel
pressure-gradient budget of `normXm1_continuousPressureDuhamel_grad_le` is
instantiated at the unique zero-box element's representative section, with
ALL four integrability leaves discharged from box data: the spacetime joint
integrability, the `s ↦ normXm1` integrability, the per-time weighted
integrability, and the `X⁰`-square integrability all hold because the
pressure of the zero-box representative vanishes literally and the coordinate
`X⁰` mass is `0` a.e.  The budget closes at `0`. -/
theorem zeroBox_fixedPoint_pressureDuhamel_grad_normXm1_eq_zero
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x : zeroBox ν T) (t : ℝ) (i : Fin 3) :
    normXm1 (fun ξ : ES => ∫ s in Icc (0 : ℝ) t,
        heatMode (ν : ℝ) (t - s)
          (fun ζ : ES => (ζ i : ℂ) •
            continuousPressureSource (everywhereRawRepresentative ν T x.1) s ζ) ξ) = 0 := by
  set u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1 with hu_def
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hps (s : ℝ) : continuousPressureSource u s = 0 :=
    zeroBox_pressSource_eq_zero ν hν T x s
  have huAES (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => u s η j) volume :=
    everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 s j
  have hu0 (s : ℝ) (j : Fin 3) : Integrable (fun η : ES => ‖u s η j‖) :=
    integrable_norm_continuousCoordinate_of_Xm1_X1 (u s) j (huAES s j)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 s j)
      (everywhereRawRepresentative_x1_integrable ν T x.1 s j)
  have hb : Integrable (fun p : ES × ℝ =>
      (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u p.2 ζ) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
    have heq : (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u p.2 ζ) p.1) =
        fun _ => (0 : ℂ) := by
      funext p
      have hfun : (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u p.2 ζ) =
          fun _ => (0 : ℂ) := by
        funext ζ
        rw [hps p.2]
        simp
      rw [hfun]
      simp [heatMode]
    rw [heq]
    simp
  have hf : Integrable (fun s : ℝ => normXm1 (heatMode (ν : ℝ) (t - s)
      (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ)))
      (volume.restrict (Icc (0 : ℝ) t)) := by
    have heq : (fun s : ℝ => normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ))) =
        fun _ => (0 : ℝ) := by
      funext s
      have hfun : (fun ζ : ES => (ζ i : ℂ) • continuousPressureSource u s ζ) =
          fun _ => (0 : ℂ) := by
        funext ζ
        rw [hps s]
        simp
      rw [hfun]
      simp [normXm1, heatMode]
    rw [heq]
    exact integrable_const 0
  have hb0 : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureSource u s ξ‖) := by
    intro s _
    have heq : (fun ξ : ES => ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureSource u s ξ‖) =
        fun _ => (0 : ℝ) := by
      funext ξ
      rw [hps s]
      simp
    rw [heq]
    simp
  have h0 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
      (volume.restrict (Icc (0 : ℝ) t)) := by
    have heq : (fun s : ℝ => coordinateX0Mass (u s) ^ 2) = fun _ => (0 : ℝ) := by
      funext s
      rw [coordinateX0Mass_eq_zero_of_ae (u s) (zeroBox_rep_ae_zero ν hν T x s)]
      simp
    rw [heq]
    exact integrable_const 0
  refine le_antisymm ?_ (normXm1_nonneg _)
  refine (normXm1_continuousPressureDuhamel_grad_le u (ν : ℝ) t i hνr huAES hu0 hb hf hb0 h0).trans
    ?_
  have hrhs : (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (u s) ^ 2) = 0 := by
    have : (fun s : ℝ => coordinateX0Mass (u s) ^ 2) = fun _ => (0 : ℝ) := by
      funext s
      rw [coordinateX0Mass_eq_zero_of_ae (u s) (zeroBox_rep_ae_zero ν hν T x s)]
      simp
    rw [this]
    simp
  rw [hrhs]

/-- **The feed instantiated on a general box, conditionally.**  For a box
element of radius `2R`, the same Duhamel pressure-gradient budget holds with
the right-hand side transported through the interpolated coordinate bound to
`4 ν⁻¹ R²`, with the exact travelling premises named: the three spacetime
per-time integrability leaves `hb`, `hf`, `h0` are the honest residual for
non-zero boxes (they require joint measurability of
`(ξ, s) ↦ p̂(rep s) ξ`, which the zero box escapes only because its pressure
vanishes literally).  The measurability and per-time integrability premises
`huAES`/`hu0` are NOT assumed here: they are derived from the box. -/
theorem pressureDuhamel_grad_normXm1_le_of_feed (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3)
    (hb : Integrable (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => (ζ i : ℂ) •
          continuousPressureSource (everywhereRawRepresentative ν T x.1) p.2 ζ) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : Integrable (fun s : ℝ => normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => (ζ i : ℂ) •
          continuousPressureSource (everywhereRawRepresentative ν T x.1) s ζ)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (h0 : Integrable (fun s : ℝ => coordinateX0Mass
        (everywhereRawRepresentative ν T x.1 s) ^ 2) (volume.restrict (Icc (0 : ℝ) t))) :
    normXm1 (fun ξ : ES => ∫ s in Icc (0 : ℝ) t,
        heatMode (ν : ℝ) (t - s)
          (fun ζ : ES => (ζ i : ℂ) •
            continuousPressureSource (everywhereRawRepresentative ν T x.1) s ζ) ξ) ≤
      4 * (ν : ℝ)⁻¹ * R ^ 2 := by
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hR0 : 0 ≤ (2 : ℝ) * R := le_trans (norm_nonneg _) x.property.1
  set u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1 with hu_def
  have huAES (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => u s η j) volume :=
    everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 s j
  have hu0 (s : ℝ) (j : Fin 3) : Integrable (fun η : ES => ‖u s η j‖) :=
    integrable_norm_continuousCoordinate_of_Xm1_X1 (u s) j (huAES s j)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 s j)
      (everywhereRawRepresentative_x1_integrable ν T x.1 s j)
  have hb0 : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖(ξ i : ℂ) • continuousPressureSource u s ξ‖) := by
    intro s _
    exact integrable_pressureDuhamel_coord (u s) i (huAES s) (hu0 s)
  have hle : volume.restrict (Icc (0 : ℝ) t) ≤ leiLinTimeMeasure T :=
    Measure.restrict_mono (Icc_subset_Icc (le_refl 0) ht.2) le_rfl
  have hX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
      (volume.restrict (Icc (0 : ℝ) t)) :=
    (coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x.1).mono_measure hle
  have hbound0 : ∀ s ∈ Icc (0 : ℝ) t,
      coordinateX0Mass (u s) ^ 2 ≤ (2 * R) * coordinateX1Mass (u s) := by
    intro s _
    calc coordinateX0Mass (u s) ^ 2
        ≤ coordinateXm1Mass (u s) * coordinateX1Mass (u s) :=
          coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass (u s)
            (everywhereRawRepresentative_xm1_integrable ν T x.1 s)
            (everywhereRawRepresentative_x1_integrable ν T x.1 s)
      _ ≤ (2 * R) * coordinateX1Mass (u s) :=
          mul_le_mul_of_nonneg_right
            ((coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 s).trans
              x.property.1)
            (coordinateX1Mass_nonneg (u s))
  refine le_trans (normXm1_continuousPressureDuhamel_grad_le u (ν : ℝ) t i hνr
    huAES hu0 hb hf hb0 h0) ?_
  have hmid : (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (u s) ^ 2) ≤
      (2 * R) * ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) := by
    have hpull : (∫ s in Icc (0 : ℝ) t, (2 * R) * coordinateX1Mass (u s)) =
        (2 * R) * ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) := by
      show ∫ s, (2 * R) • coordinateX1Mass (u s) ∂(volume.restrict (Icc (0 : ℝ) t)) =
          (2 * R) • ∫ s, coordinateX1Mass (u s) ∂(volume.restrict (Icc (0 : ℝ) t))
      exact integral_smul _ _
    exact (setIntegral_mono_on h0 (hX1int.const_mul (2 * R))
        isClosed_Icc.measurableSet hbound0).trans hpull.le
  refine hmid.trans ?_
  have htail : (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s)) ≤
      ∫ s, coordinateX1Mass (u s) ∂(leiLinTimeMeasure T) :=
    integral_mono_measure hle
      (ae_of_all (leiLinTimeMeasure T) fun s => coordinateX1Mass_nonneg (u s))
      (coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x.1)
  have hchain := integral_coordinateX1Mass_rep_le ν hν T R x
  calc (2 * R) * ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s)
      ≤ (2 * R) * ∫ s, coordinateX1Mass (u s) ∂(leiLinTimeMeasure T) :=
        mul_le_mul_of_nonneg_left htail hR0
    _ ≤ (2 * R) * (2 * (ν : ℝ)⁻¹ * R) :=
        mul_le_mul_of_nonneg_left hchain hR0
    _ = 4 * (ν : ℝ)⁻¹ * R ^ 2 := by ring

/-! ## Consumption of the landed physical-pairing flagship -/

/-- **The flagship physical pairing at a box element's representative
section.**  `continuousPressurePhysical_pairing_physicalLaplacian` (landed in
`ContinuousLeiLinPressurePhysical`) is instantiated at
`everywhereRawRepresentative ν T x.1 t`: the `AES` premise is the box
carrier's own measurability, and the coordinate `L¹` premise is discharged
here by the `X⁻¹ + X¹` interpolation of `‖u ξ i‖` (`Integrable` follows from
the box's weighted integrability — no new hypothesis travels).  This is the
fixed-point-side data feeding the primitive's remaining named obligation. -/
theorem continuousPressurePhysical_pairing_rep (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) (t : ℝ) (ψ : 𝓢(ES, ℂ)) :
    ∫ y : ES, continuousPressurePhysical (everywhereRawRepresentative ν T x.1 t) y •
        ⇑(physicalLaplacian ψ) y =
      ((2 * Real.pi : ℂ) ^ 2) * ∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) * ((fun η : ES => (everywhereRawRepresentative ν T x.1 t) η i)
            ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η : ES => (everywhereRawRepresentative ν T x.1 t) η j)) ξ) *
          𝓕⁻ ⇑ψ ξ :=
  continuousPressurePhysical_pairing_physicalLaplacian (everywhereRawRepresentative ν T x.1 t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t)
    (fun j => integrable_norm_continuousCoordinate_of_Xm1_X1
      (everywhereRawRepresentative ν T x.1 t) j
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 t j)
      (everywhereRawRepresentative_xm1_integrable ν T x.1 t j)
      (everywhereRawRepresentative_x1_integrable ν T x.1 t j)) ψ

end Navier.Analysis.ContinuousLeiLinMildFixedPointPressure

set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.integrable_norm_continuousCoordinate_of_Xm1_X1
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.continuousPressureFourier_congr_ae
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.zeroBox_rep_ae_zero
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.record_zeroBox
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.existsUnique_mildFixedPoint_zeroBox
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.normX1_continuousPressureFourier_rep_le
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.fixedPoint_pressureEq
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.pressureDuhamel_grad_normXm1_le_of_feed
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.continuousPressurePhysical_pairing_rep

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.integrable_norm_continuousCoordinate_of_Xm1_X1
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.coordinateX0Mass_le_coordinateXm1Mass_add_coordinateX1Mass
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.continuousPressureFourier_congr_ae
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.zeroBox_rep_ae_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.zeroBox_mildImage_eq_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.record_zeroBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.existsUnique_mildFixedPoint_zeroBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.hjointDiag_matching_of_continuous
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.hjointL_matching
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.hjointR_matching
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.normX1_continuousPressureFourier_rep_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.normXm1_continuousPressureGrad_rep_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.integral_coordinateX1Mass_rep_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.fixedPoint_pressureEq
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.zeroBox_fixedPoint_pressureDuhamel_grad_normXm1_eq_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.pressureDuhamel_grad_normXm1_le_of_feed
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.continuousPressurePhysical_pairing_rep
