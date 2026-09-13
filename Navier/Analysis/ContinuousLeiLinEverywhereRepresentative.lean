import Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability

/-!
# An everywhere integrable representative of the linked trajectory quotient

The canonical `X⁻¹` and viscous `X¹` Bochner representatives agree only for
almost every time.  Pointwise analytic estimates, however, quantify over every
time in the causal interval.  We therefore replace the canonical field by zero
at the exceptional times.  The resulting raw field has both defining spatial
moments at every time and is unchanged in both completed trajectory slots.
No continuous representative or closedness of continuous representatives is
assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability

namespace Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

/-- At a good time the two canonical spatial representatives agree and the
canonical `X⁻¹` representative also carries the unscaled `X¹` moment. -/
def RepresentativeGoodAt (ν : ℝ≥0) (T : ℝ)
    (x : ActualLinkedCarrier ν T) (t : ℝ) : Prop :=
  xm1RawRepresentative ν T x t =ᵐ[volume]
      viscousX1RawRepresentative ν T x t ∧
    (∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖xm1RawRepresentative ν T x t ξ i‖)) ∧
    ‖((x.1.fst : Xm1TimeSlot T) t)‖ ≤ ‖(x.1.fst : Xm1TimeSlot T)‖

/-- The canonical representative of an `L∞` time slot is bounded almost
everywhere by the slot norm itself. -/
theorem xm1TimeSlot_norm_ae
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      ‖((x.1.fst : Xm1TimeSlot T) t)‖ ≤ ‖(x.1.fst : Xm1TimeSlot T)‖ := by
  have h := ae_le_lpNorm_exponent_top
    (Lp.memLp (x.1.fst : Xm1TimeSlot T))
  have hnorm : lpNorm (fun t => (x.1.fst : Xm1TimeSlot T) t) ∞
      (leiLinTimeMeasure T) = ‖(x.1.fst : Xm1TimeSlot T)‖ := by
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable (x.1.fst : Xm1TimeSlot T)),
      ← Lp.norm_def]
  simpa only [hnorm] using h

/-- The linked quotient is good at almost every horizon time. -/
theorem representativeGoodAt_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T, RepresentativeGoodAt ν T x t := by
  filter_upwards [raw_representatives_ae ν hν T x,
    xm1RawRepresentative_x1_integrable_ae ν hν T x,
    xm1TimeSlot_norm_ae ν T x] with t hrep hx1 hnorm
  exact ⟨hrep, hx1, hnorm⟩

/-- A single raw representative with both spatial moments at every time:
retain the canonical `X⁻¹` representative at good times and use zero on the
null exceptional time set. -/
noncomputable def everywhereRawRepresentative (ν : ℝ≥0) (T : ℝ)
    (x : ActualLinkedCarrier ν T) : ℝ → ES → ComplexSpace := by
  classical
  exact fun t => if RepresentativeGoodAt ν T x t then
    xm1RawRepresentative ν T x t else 0

/-- The everywhere representative is the canonical `X⁻¹` representative for
almost every horizon time. -/
theorem everywhereRawRepresentative_eq_xm1_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      everywhereRawRepresentative ν T x t = xm1RawRepresentative ν T x t := by
  filter_upwards [representativeGoodAt_ae ν hν T x] with t ht
  simp [everywhereRawRepresentative, ht]

/-- The everywhere representative agrees with the canonical viscous `X¹`
representative for almost every time and frequency. -/
theorem everywhereRawRepresentative_eq_viscous_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      everywhereRawRepresentative ν T x t =ᵐ[volume]
        viscousX1RawRepresentative ν T x t := by
  filter_upwards [representativeGoodAt_ae ν hν T x] with t ht
  simpa [everywhereRawRepresentative, ht] using ht.1

/-- Every time section has the literal `X⁻¹` coordinate integrability. -/
theorem everywhereRawRepresentative_xm1_integrable
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖everywhereRawRepresentative ν T x t ξ i‖) := by
  by_cases ht : RepresentativeGoodAt ν T x t
  · simpa [everywhereRawRepresentative, ht] using
      xm1RawRepresentative_integrable ν T x t i
  · simp [everywhereRawRepresentative, ht]

/-- Every time section has the literal unscaled `X¹` coordinate integrability. -/
theorem everywhereRawRepresentative_x1_integrable
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ *
      ‖everywhereRawRepresentative ν T x t ξ i‖) := by
  by_cases ht : RepresentativeGoodAt ν T x t
  · simpa [everywhereRawRepresentative, ht] using ht.2.1 i
  · simp [everywhereRawRepresentative, ht]

/-- Each canonical `X⁻¹` coordinate is strongly measurable with respect to
Lebesgue measure. -/
theorem xm1RawRepresentative_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES => xm1RawRepresentative ν T x t ξ i)
      volume := by
  have hac : volume ≪ xm1FrequencyMeasure :=
    (volume_absolutelyContinuous_commonFrequencyMeasure ν hν).trans
      (Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_xm1 ν))
  have hvec : AEStronglyMeasurable
      (fun ξ : ES => (((x.1.fst : Xm1TimeSlot T) t : Xm1Spatial) ξ :
        FourierCoordinateL1)) volume :=
    (Lp.aestronglyMeasurable ((x.1.fst : Xm1TimeSlot T) t)).mono_ac hac
  exact (PiLp.continuous_apply 1 (fun _ : Fin 3 => ℂ) i).aestronglyMeasurable
    |>.comp_aemeasurable hvec.aemeasurable

/-- Every section of the modified representative is strongly measurable in
frequency, including exceptional times where it is zero. -/
theorem everywhereRawRepresentative_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable
      (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i) volume := by
  by_cases ht : RepresentativeGoodAt ν T x t
  · simpa [everywhereRawRepresentative, ht] using
      xm1RawRepresentative_aestronglyMeasurable ν hν T x t i
  · simpa [everywhereRawRepresentative, ht] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume)

/-- The `X⁻¹` section built from the everywhere representative. -/
def everywhereXm1Section
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ℝ → Xm1Spatial :=
  xm1Section (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_xm1_integrable ν T x)

/-- The viscous `X¹` section built from the same everywhere representative. -/
def everywhereViscousX1Section
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ℝ → ViscousX1Spatial ν :=
  viscousX1Section (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_x1_integrable ν T x) ν

/-- At each good time, rebuilding the `X⁻¹` spatial quotient recovers its
canonical value exactly. -/
theorem everywhereXm1Section_eq_at_good
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (t : ℝ) (ht : RepresentativeGoodAt ν T x t) :
    everywhereXm1Section ν hν T x t = (x.1.fst : Xm1TimeSlot T) t := by
  apply Lp.ext
  have hcoe := coeFn_toXm1Spatial
    (everywhereRawRepresentative ν T x t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
    (everywhereRawRepresentative_xm1_integrable ν T x t)
  filter_upwards [hcoe] with ξ hξ
  have hξ' : ((everywhereXm1Section ν hν T x t : Xm1Spatial) ξ) =
      coordinateL1 (everywhereRawRepresentative ν T x t) ξ := by
    simpa only [everywhereXm1Section, xm1Section] using hξ
  rw [hξ']
  simp [coordinateL1, everywhereRawRepresentative, ht, xm1RawRepresentative]

/-- At each good time, rebuilding the viscous `X¹` quotient also recovers
its canonical value exactly. -/
theorem everywhereViscousX1Section_eq_at_good
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (t : ℝ) (ht : RepresentativeGoodAt ν T x t) :
    everywhereViscousX1Section ν hν T x t =
      (x.1.snd : ViscousX1TimeSlot ν T) t := by
  apply Lp.ext
  have hcoe := coeFn_toViscousX1Spatial ν
    (everywhereRawRepresentative ν T x t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
    (everywhereRawRepresentative_x1_integrable ν T x t)
  have hrep : everywhereRawRepresentative ν T x t =ᵐ[viscousX1FrequencyMeasure ν]
      viscousX1RawRepresentative ν T x t :=
    (withDensity_absolutelyContinuous volume (viscousX1Density ν)).ae_eq <| by
      simpa [everywhereRawRepresentative, ht] using ht.1
  filter_upwards [hcoe, hrep] with ξ hξ hrepξ
  have hξ' : ((everywhereViscousX1Section ν hν T x t :
      ViscousX1Spatial ν) ξ) =
      coordinateL1 (everywhereRawRepresentative ν T x t) ξ := by
    simpa only [everywhereViscousX1Section, viscousX1Section] using hξ
  rw [hξ', show coordinateL1 (everywhereRawRepresentative ν T x t) ξ =
      coordinateL1 (viscousX1RawRepresentative ν T x t) ξ from
    congrArg (WithLp.toLp 1) hrepξ]
  simp [coordinateL1, viscousX1RawRepresentative]

/-- The rebuilt `X⁻¹` section is the original outer `L∞` representative almost
everywhere in time. -/
theorem everywhereXm1Section_eq_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    everywhereXm1Section ν hν T x =ᵐ[leiLinTimeMeasure T]
      fun t => (x.1.fst : Xm1TimeSlot T) t := by
  exact (representativeGoodAt_ae ν hν T x).mono fun t ht =>
    everywhereXm1Section_eq_at_good ν hν T x t ht

/-- The rebuilt viscous `X¹` section is likewise the original outer `L¹`
representative almost everywhere in time. -/
theorem everywhereViscousX1Section_eq_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    everywhereViscousX1Section ν hν T x =ᵐ[leiLinTimeMeasure T]
      fun t => (x.1.snd : ViscousX1TimeSlot ν T) t := by
  exact (representativeGoodAt_ae ν hν T x).mono fun t ht =>
    everywhereViscousX1Section_eq_at_good ν hν T x t ht

/-- The rebuilt `X⁻¹` section is strongly measurable in time because it is
equal almost everywhere to the original Bochner representative. -/
theorem everywhereXm1Section_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (everywhereXm1Section ν hν T x)
      (leiLinTimeMeasure T) := by
  exact (Lp.aestronglyMeasurable (x.1.fst : Xm1TimeSlot T)).congr
    (everywhereXm1Section_eq_ae ν hν T x).symm

/-- The rebuilt viscous `X¹` section is strongly measurable in time for the
same representative-invariance reason. -/
theorem everywhereViscousX1Section_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (everywhereViscousX1Section ν hν T x)
      (leiLinTimeMeasure T) := by
  exact (Lp.aestronglyMeasurable (x.1.snd : ViscousX1TimeSlot ν T)).congr
    (everywhereViscousX1Section_eq_ae ν hν T x).symm

/-- Null-set repair upgrades the essential `X⁻¹` bound to a pointwise bound
at every real time. -/
theorem coordinateXm1Mass_everywhereRawRepresentative_le
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) :
    coordinateXm1Mass (everywhereRawRepresentative ν T x t) ≤
      ‖(x.1.fst : Xm1TimeSlot T)‖ := by
  by_cases ht : RepresentativeGoodAt ν T x t
  · rw [← norm_xm1Section
      (everywhereRawRepresentative ν T x)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
      (everywhereRawRepresentative_xm1_integrable ν T x) t,
      show xm1Section (everywhereRawRepresentative ν T x)
          (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
          (everywhereRawRepresentative_xm1_integrable ν T x) t =
        everywhereXm1Section ν hν T x t from rfl,
      everywhereXm1Section_eq_at_good ν hν T x t ht]
    exact ht.2.2
  · simp [everywhereRawRepresentative, ht, coordinateXm1Mass, normXm1]

/-- The unscaled `X¹` coordinate mass of the everywhere representative is
integrable in time; positivity of viscosity removes the scale built into the
completed viscous slot. -/
theorem coordinateX1Mass_everywhereRawRepresentative_integrable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    Integrable (fun t => coordinateX1Mass
      (everywhereRawRepresentative ν T x t)) (leiLinTimeMeasure T) := by
  have horig : Integrable
      (fun t => ‖((x.1.snd : ViscousX1TimeSlot ν T) t)‖)
      (leiLinTimeMeasure T) :=
    (memLp_one_iff_integrable.mp
      (Lp.memLp (x.1.snd : ViscousX1TimeSlot ν T))).norm
  have hsection : Integrable
      (fun t => ‖everywhereViscousX1Section ν hν T x t‖)
      (leiLinTimeMeasure T) := by
    apply horig.congr
    filter_upwards [everywhereViscousX1Section_eq_ae ν hν T x] with t ht
    rw [ht]
  have hscaled : Integrable (fun t => (ν : ℝ) * coordinateX1Mass
      (everywhereRawRepresentative ν T x t)) (leiLinTimeMeasure T) := by
    apply hsection.congr
    filter_upwards with t
    exact norm_viscousX1Section
      (everywhereRawRepresentative ν T x)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
      (everywhereRawRepresentative_x1_integrable ν T x) ν t
  have hunscaled := hscaled.const_mul ((ν : ℝ)⁻¹)
  apply hunscaled.congr
  filter_upwards with t
  field_simp

/-- The actual `L∞_t X⁻¹` slot rebuilt from the everywhere representative. -/
def everywhereXm1TimeSlot
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    Xm1TimeSlot T :=
  toXm1TimeSlot (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_xm1_integrable ν T x)
    T ‖(x.1.fst : Xm1TimeSlot T)‖
    (everywhereXm1Section_aestronglyMeasurable ν hν T x)
    (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x t)

/-- The actual `L¹_t(νX¹)` slot rebuilt from the same representative. -/
def everywhereViscousX1TimeSlot
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ViscousX1TimeSlot ν T :=
  toViscousX1TimeSlot (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_x1_integrable ν T x)
    ν T (everywhereViscousX1Section_aestronglyMeasurable ν hν T x)
    (coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x)

/-- Rebuilding the outer `X⁻¹` quotient from the repaired field is the
identity on the original slot. -/
theorem everywhereXm1TimeSlot_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    everywhereXm1TimeSlot ν hν T x = (x.1.fst : Xm1TimeSlot T) := by
  apply Lp.ext
  have hcoe := coeFn_toXm1TimeSlot
    (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_xm1_integrable ν T x)
    T ‖(x.1.fst : Xm1TimeSlot T)‖
    (everywhereXm1Section_aestronglyMeasurable ν hν T x)
    (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x t)
  filter_upwards [hcoe, everywhereXm1Section_eq_ae ν hν T x] with t hcoe_t hsection_t
  have hcoe_t' : everywhereXm1TimeSlot ν hν T x t =
      everywhereXm1Section ν hν T x t := by
    simpa only [everywhereXm1TimeSlot, everywhereXm1Section] using hcoe_t
  rw [hcoe_t', hsection_t]

/-- Rebuilding the outer viscous `X¹` quotient is also the identity. -/
theorem everywhereViscousX1TimeSlot_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    everywhereViscousX1TimeSlot ν hν T x =
      (x.1.snd : ViscousX1TimeSlot ν T) := by
  apply Lp.ext
  have hcoe := coeFn_toViscousX1TimeSlot
    (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_x1_integrable ν T x)
    ν T (everywhereViscousX1Section_aestronglyMeasurable ν hν T x)
    (coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x)
  filter_upwards [hcoe, everywhereViscousX1Section_eq_ae ν hν T x] with
    t hcoe_t hsection_t
  have hcoe_t' : everywhereViscousX1TimeSlot ν hν T x t =
      everywhereViscousX1Section ν hν T x t := by
    simpa only [everywhereViscousX1TimeSlot, everywhereViscousX1Section] using hcoe_t
  rw [hcoe_t', hsection_t]

/-- The repaired raw field constructs a linked carrier element using only the
norms already present in `x`. -/
def actualLinkedEverywhereRepresentative
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ActualLinkedCarrier ν T :=
  actualLinkedOfRaw ν T ‖(x.1.fst : Xm1TimeSlot T)‖
    (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_xm1_integrable ν T x)
    (everywhereRawRepresentative_x1_integrable ν T x)
    (everywhereXm1Section_aestronglyMeasurable ν hν T x)
    (everywhereViscousX1Section_aestronglyMeasurable ν hν T x)
    (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x t)
    (coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x)

/-- Original carrier consumer: replacing exceptional times by zero and then
rebuilding both quotient slots leaves the actual linked trajectory unchanged. -/
theorem actualLinkedEverywhereRepresentative_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    actualLinkedEverywhereRepresentative ν hν T x = x := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 1
  apply Prod.ext
  · exact everywhereXm1TimeSlot_eq ν hν T x
  · exact everywhereViscousX1TimeSlot_eq ν hν T x

end Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.representativeGoodAt_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative_eq_xm1_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative_eq_viscous_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative_xm1_integrable
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative_x1_integrable
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereRawRepresentative_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.xm1TimeSlot_norm_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereXm1Section_eq_at_good
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereViscousX1Section_eq_at_good
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereXm1Section_eq_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereViscousX1Section_eq_ae
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.coordinateXm1Mass_everywhereRawRepresentative_le
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.coordinateX1Mass_everywhereRawRepresentative_integrable
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereXm1TimeSlot_eq
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.everywhereViscousX1TimeSlot_eq
#print axioms Navier.Analysis.ContinuousLeiLinEverywhereRepresentative.actualLinkedEverywhereRepresentative_eq
