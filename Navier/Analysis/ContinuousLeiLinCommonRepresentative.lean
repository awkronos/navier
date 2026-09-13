import Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

/-!
# Common raw representatives of the actual linked Lei--Lin carrier

This file opens the concrete linked `L∞_t X⁻¹ ∩ L¹_t νX¹` carrier without
assuming that its equivalence classes contain continuous representatives.  Its
two canonical Bochner representatives agree for almost every time after
restriction to the common positive-density frequency measure, and hence their
underlying Fourier fields agree for Lebesgue-almost every frequency.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots

namespace Navier.Analysis.ContinuousLeiLinCommonRepresentative

/-- The canonical raw Fourier field selected from the `X⁻¹` component of the
actual linked carrier.  No continuity is asserted for this representative. -/
def xm1RawRepresentative (ν : ℝ≥0) (T : ℝ)
    (x : ActualLinkedCarrier ν T) : ℝ → ES → ComplexSpace :=
  fun t ξ => (((x.1.fst : Xm1TimeSlot T) t : Xm1Spatial) ξ : FourierCoordinateL1).ofLp

/-- The canonical raw Fourier field selected from the viscosity-weighted
`X¹` component. -/
def viscousX1RawRepresentative (ν : ℝ≥0) (T : ℝ)
    (x : ActualLinkedCarrier ν T) : ℝ → ES → ComplexSpace :=
  fun t ξ => (((x.1.snd : ViscousX1TimeSlot ν T) t : ViscousX1Spatial ν) ξ :
    FourierCoordinateL1).ofLp

/-- The two spatial representatives of a linked trajectory agree in the
common spatial quotient for almost every time. -/
theorem linked_spatial_representatives_ae
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      xm1SpatialToCommon ν ((x.1.fst : Xm1TimeSlot T) t) =
        viscousX1SpatialToCommon ν ((x.1.snd : ViscousX1TimeSlot ν T) t) := by
  let μ := leiLinTimeMeasure T
  let xm : Xm1TimeSlot T := x.1.fst
  let x1 : ViscousX1TimeSlot ν T := x.1.snd
  let xmCommonTop := (xm1SpatialToCommon ν).compLpL ∞ μ xm
  have hxmOuter : ∀ᵐ t ∂μ,
      ((lpTopToLpOne μ xmCommonTop : CommonTrajectorySlot ν T) t) =
        (xmCommonTop t) := by
    filter_upwards with t
    rfl
  have hxmInner : ∀ᵐ t ∂μ,
      xmCommonTop t = xm1SpatialToCommon ν (xm t) := by
    exact (xm1SpatialToCommon ν).coeFn_compLpL xm
  have hx1Inner : ∀ᵐ t ∂μ,
      (((viscousX1SpatialToCommon ν).compLpL 1 μ x1 :
        CommonTrajectorySlot ν T) t) =
          viscousX1SpatialToCommon ν (x1 t) := by
    exact (viscousX1SpatialToCommon ν).coeFn_compLpL x1
  have hlinked : realizeXm1Trajectory ν T xm =
      realizeViscousX1Trajectory ν T x1 := by
    exact x.property
  have hreal : ∀ᵐ t ∂μ,
      (realizeXm1Trajectory ν T xm : CommonTrajectorySlot ν T) t =
        (realizeViscousX1Trajectory ν T x1 : CommonTrajectorySlot ν T) t := by
    rw [hlinked]
    filter_upwards with t
    rfl
  filter_upwards [hxmOuter, hxmInner, hx1Inner, hreal] with t hxo hxi h1i hr
  change xm1SpatialToCommon ν (xm t) = viscousX1SpatialToCommon ν (x1 t)
  have hr' :
      ((lpTopToLpOne μ xmCommonTop : CommonTrajectorySlot ν T) t) =
        (((viscousX1SpatialToCommon ν).compLpL 1 μ x1 :
          CommonTrajectorySlot ν T) t) := by
    simpa [realizeXm1Trajectory, realizeViscousX1Trajectory, μ, xmCommonTop] using hr
  exact hxi.symm.trans (hxo.symm.trans (hr'.trans h1i))

/-- At positive viscosity the common-measure linkage identifies the two raw
Fourier representatives for almost every time and Lebesgue frequency. -/
theorem raw_representatives_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      xm1RawRepresentative ν T x t =ᵐ[volume]
        viscousX1RawRepresentative ν T x t := by
  have htime := linked_spatial_representatives_ae ν T x
  filter_upwards [htime] with t ht
  apply (volume_absolutelyContinuous_commonFrequencyMeasure ν hν).ae_eq
  have hxm : xm1SpatialToCommon ν ((x.1.fst : Xm1TimeSlot T) t)
      =ᵐ[commonFrequencyMeasure ν] ((x.1.fst : Xm1TimeSlot T) t) := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_xm1 ν)
      ((x.1.fst : Xm1TimeSlot T) t)
  have hx1 : viscousX1SpatialToCommon ν ((x.1.snd : ViscousX1TimeSlot ν T) t)
      =ᵐ[commonFrequencyMeasure ν] ((x.1.snd : ViscousX1TimeSlot ν T) t) := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_viscousX1 ν)
      ((x.1.snd : ViscousX1TimeSlot ν T) t)
  filter_upwards [hxm, hx1] with ξ hxmξ hx1ξ
  have hcoord :
      (((x.1.fst : Xm1TimeSlot T) t : Xm1Spatial) ξ : FourierCoordinateL1) =
        (((x.1.snd : ViscousX1TimeSlot ν T) t : ViscousX1Spatial ν) ξ :
          FourierCoordinateL1) := by
    rw [← hxmξ, ← hx1ξ, ht]
  exact congrArg (fun z : FourierCoordinateL1 => z.ofLp) hcoord

end Navier.Analysis.ContinuousLeiLinCommonRepresentative

#print axioms Navier.Analysis.ContinuousLeiLinCommonRepresentative.linked_spatial_representatives_ae
#print axioms Navier.Analysis.ContinuousLeiLinCommonRepresentative.raw_representatives_ae
