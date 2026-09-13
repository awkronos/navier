import Navier.Analysis.ContinuousLeiLinActualSlots
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Raw Fourier trajectories in the concrete Lei--Lin slots

This module connects the pointwise Fourier fields used by the existing
whole-space mild-map estimates to the complete nested Bochner spaces from
`ContinuousLeiLinActualSlots`.

The pointwise carrier is `PiLp 1 (Fin 3 → ℂ)`, so its norm is literally the
sum of the three coordinate norms. Integrability against the actual densities
turns the repository's coordinate `X⁻¹` and `X¹` masses into exact spatial `L¹`
norms. A uniform finite-horizon `X⁻¹` bound constructs the time `L∞` slot,
while the existing integrated `X¹` budget constructs the time `L¹` slot. Their
representatives agree in the common spacetime carrier because they come from
the same raw field.

For the continuous mild image, the only regularity input left explicit here
is strong measurability of the two maps into the weighted spatial `L¹` spaces.
The norm and common-representative obligations are discharged in this file;
no fixed-point or self-map conclusion is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots

namespace Navier.Analysis.ContinuousLeiLinTrajectoryLift

def coordinateL1 (u : ES → ComplexSpace) (ξ : ES) : FourierCoordinateL1 :=
  WithLp.toLp 1 (u ξ)

@[simp] theorem coordinateL1_apply (u : ES → ComplexSpace) (ξ : ES) (i : Fin 3) :
    coordinateL1 u ξ i = u ξ i := rfl

@[simp] theorem norm_coordinateL1 (u : ES → ComplexSpace) (ξ : ES) :
    ‖coordinateL1 u ξ‖ = ∑ i : Fin 3, ‖u ξ i‖ := by
  exact PiLp.norm_eq_of_L1 _

 theorem coordinateL1_aestronglyMeasurable
    (u : ES → ComplexSpace)
    (hu : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume) :
    AEStronglyMeasurable (coordinateL1 u) volume := by
  apply (PiLp.continuous_toLp 1 (fun _ : Fin 3 => ℂ)).aestronglyMeasurable.comp_aemeasurable
  exact (aemeasurable_pi_lambda _ fun i => (hu i).aemeasurable)

 theorem xm1Density_toReal_ae :
    ∀ᵐ ξ : ES ∂volume, (xm1Density ξ).toReal = ‖ξ‖⁻¹ := by
  have hzero : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with ξ hξ
  simp [xm1Density, norm_pos_iff.mpr hξ]

theorem coordinateL1_xm1_integrable
    (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖)) :
    Integrable (coordinateL1 u) xm1FrequencyMeasure := by
  change Integrable (coordinateL1 u)
    (volume.withDensity (fun ξ : ES => ENNReal.ofReal (‖ξ‖⁻¹)))
  refine (integrable_withDensity_iff_integrable_smul'
    (μ := volume) (g := coordinateL1 u)
    (ENNReal.measurable_ofReal.comp measurable_norm.inv)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2 ?_
  change Integrable
    (fun ξ : ES => (ENNReal.ofReal (‖ξ‖⁻¹)).toReal • coordinateL1 u ξ) volume
  have hvM : AEStronglyMeasurable (coordinateL1 u) volume :=
    coordinateL1_aestronglyMeasurable u huM
  have hdM : AEStronglyMeasurable
      (fun ξ : ES => (ENNReal.ofReal (‖ξ‖⁻¹)).toReal) volume :=
    ((ENNReal.measurable_ofReal.comp measurable_norm.inv).ennreal_toReal).aestronglyMeasurable
  have hweightedM : AEStronglyMeasurable
      (fun ξ : ES => (ENNReal.ofReal (‖ξ‖⁻¹)).toReal • coordinateL1 u ξ) volume :=
    hdM.smul hvM
  apply (integrable_norm_iff hweightedM).mp
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ‖ξ‖⁻¹ * ‖u ξ i‖) :=
    integrable_finsetSum Finset.univ (fun i _ => huI i)
  apply hsum.congr
  filter_upwards [] with ξ
  rw [norm_smul, norm_coordinateL1, Finset.mul_sum]
  simp [inv_nonneg.mpr (norm_nonneg ξ)]

theorem viscousX1Density_toReal (ν : ℝ≥0) (ξ : ES) :
    (viscousX1Density ν ξ).toReal = (ν : ℝ) * ‖ξ‖ := by
  simp [viscousX1Density]

theorem coordinateL1_viscousX1_integrable
    (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    Integrable (coordinateL1 u) (viscousX1FrequencyMeasure ν) := by
  change Integrable (coordinateL1 u)
    (volume.withDensity (fun ξ : ES => (ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖))
  refine (integrable_withDensity_iff_integrable_smul'
    (μ := volume) (g := coordinateL1 u)
    (measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_norm))
    (Eventually.of_forall fun _ => ENNReal.mul_lt_top ENNReal.coe_lt_top
      ENNReal.ofReal_lt_top)).2 ?_
  change Integrable (fun ξ : ES =>
    ((ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖).toReal • coordinateL1 u ξ) volume
  have hvM : AEStronglyMeasurable (coordinateL1 u) volume :=
    coordinateL1_aestronglyMeasurable u huM
  have hdM : AEStronglyMeasurable (fun ξ : ES =>
      ((ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖).toReal) volume :=
    (measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_norm))
      |>.ennreal_toReal.aestronglyMeasurable
  have hweightedM : AEStronglyMeasurable (fun ξ : ES =>
      ((ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖).toReal • coordinateL1 u ξ) volume :=
    hdM.smul hvM
  apply (integrable_norm_iff hweightedM).mp
  have hsum : Integrable (fun ξ : ES =>
      ∑ i : Fin 3, (ν : ℝ) * (‖ξ‖ * ‖u ξ i‖)) :=
    integrable_finsetSum Finset.univ (fun i _ => (huI i).const_mul (ν : ℝ))
  apply hsum.congr
  filter_upwards [] with ξ
  rw [norm_smul, norm_coordinateL1, Finset.mul_sum]
  simp [mul_assoc]

def toXm1Spatial (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖)) :
    Xm1Spatial :=
  (memLp_one_iff_integrable.mpr (coordinateL1_xm1_integrable u huM huI)).toLp
    (coordinateL1 u)

def toViscousX1Spatial (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    ViscousX1Spatial ν :=
  (memLp_one_iff_integrable.mpr
    (coordinateL1_viscousX1_integrable ν u huM huI)).toLp (coordinateL1 u)

theorem coeFn_toXm1Spatial (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖)) :
    toXm1Spatial u huM huI =ᵐ[xm1FrequencyMeasure] coordinateL1 u := by
  exact MemLp.coeFn_toLp _

theorem coeFn_toViscousX1Spatial (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    toViscousX1Spatial ν u huM huI =ᵐ[viscousX1FrequencyMeasure ν]
      coordinateL1 u := by
  exact MemLp.coeFn_toLp _

theorem integral_norm_coordinateL1_xm1_eq
    (u : ES → ComplexSpace)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖)) :
    (∫ ξ : ES, ‖coordinateL1 u ξ‖ ∂xm1FrequencyMeasure) = coordinateXm1Mass u := by
  change (∫ ξ : ES, ‖coordinateL1 u ξ‖
    ∂volume.withDensity (fun ξ : ES => ENNReal.ofReal (‖ξ‖⁻¹))) = _
  calc
    _ = ∫ ξ : ES, (ENNReal.ofReal (‖ξ‖⁻¹)).toReal •
        ‖coordinateL1 u ξ‖ ∂volume := by
      exact integral_withDensity_eq_integral_toReal_smul
        (μ := volume) (g := fun ξ : ES => ‖coordinateL1 u ξ‖)
        (ENNReal.measurable_ofReal.comp measurable_norm.inv)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    _ = coordinateXm1Mass u := by
      unfold coordinateXm1Mass normXm1
      calc
        _ = ∫ ξ : ES, ∑ i : Fin 3, ‖ξ‖⁻¹ * ‖u ξ i‖ := by
          apply integral_congr_ae
          filter_upwards [] with ξ
          rw [norm_coordinateL1]
          change (ENNReal.ofReal (‖ξ‖⁻¹)).toReal * ∑ i : Fin 3, ‖u ξ i‖ = _
          rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg ξ)), Finset.mul_sum]
        _ = ∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖⁻¹ * ‖u ξ i‖ := by
          exact integral_finsetSum Finset.univ (fun i _ => huI i)

theorem norm_toXm1Spatial
    (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖)) :
    ‖toXm1Spatial u huM huI‖ = coordinateXm1Mass u := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ ξ : ES, ‖coordinateL1 u ξ‖ ∂xm1FrequencyMeasure :=
      integral_congr_ae <| by
        filter_upwards [coeFn_toXm1Spatial u huM huI] with ξ hξ
        rw [hξ]
    _ = coordinateXm1Mass u := integral_norm_coordinateL1_xm1_eq u huI

theorem integral_norm_coordinateL1_viscousX1_eq
    (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    (∫ ξ : ES, ‖coordinateL1 u ξ‖ ∂viscousX1FrequencyMeasure ν) =
      (ν : ℝ) * coordinateX1Mass u := by
  change (∫ ξ : ES, ‖coordinateL1 u ξ‖
    ∂volume.withDensity (fun ξ : ES => (ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖)) = _
  calc
    _ = ∫ ξ : ES, (((ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖).toReal) •
        ‖coordinateL1 u ξ‖ ∂volume := by
      exact integral_withDensity_eq_integral_toReal_smul
        (μ := volume) (g := fun ξ : ES => ‖coordinateL1 u ξ‖)
        (measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_norm))
        (Eventually.of_forall fun _ => ENNReal.mul_lt_top ENNReal.coe_lt_top
          ENNReal.ofReal_lt_top)
    _ = (ν : ℝ) * coordinateX1Mass u := by
      unfold coordinateX1Mass normX1
      calc
        _ = ∫ ξ : ES, ∑ i : Fin 3, (ν : ℝ) * (‖ξ‖ * ‖u ξ i‖) := by
          apply integral_congr_ae
          filter_upwards [] with ξ
          rw [norm_coordinateL1]
          change (((ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖).toReal) *
            ∑ i : Fin 3, ‖u ξ i‖ = _
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (norm_nonneg ξ),
            Finset.mul_sum]
          simp only [mul_assoc]
        _ = ∑ i : Fin 3, ∫ ξ : ES, (ν : ℝ) * (‖ξ‖ * ‖u ξ i‖) := by
          exact integral_finsetSum Finset.univ
            (fun i _ => (huI i).const_mul (ν : ℝ))
        _ = (ν : ℝ) * ∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖ * ‖u ξ i‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]

theorem norm_toViscousX1Spatial
    (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    ‖toViscousX1Spatial ν u huM huI‖ = (ν : ℝ) * coordinateX1Mass u := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ ξ : ES, ‖coordinateL1 u ξ‖ ∂viscousX1FrequencyMeasure ν :=
      integral_congr_ae <| by
        filter_upwards [coeFn_toViscousX1Spatial ν u huM huI] with ξ hξ
        rw [hξ]
    _ = (ν : ℝ) * coordinateX1Mass u :=
      integral_norm_coordinateL1_viscousX1_eq ν u huI

/-- The two actual weighted spatial representatives built from the same raw
Fourier field agree in the common positive-density quotient. -/
theorem spatial_realizations_eq
    (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huXm1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (huX1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    xm1SpatialToCommon ν (toXm1Spatial u huM huXm1) =
      viscousX1SpatialToCommon ν (toViscousX1Spatial ν u huM huX1) := by
  apply Lp.ext
  have hcommonXm1 : commonFrequencyMeasure ν ≪ xm1FrequencyMeasure :=
    Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_xm1 ν)
  have hcommonX1 : commonFrequencyMeasure ν ≪ viscousX1FrequencyMeasure ν :=
    Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_viscousX1 ν)
  have hxmRep : toXm1Spatial u huM huXm1 =ᵐ[commonFrequencyMeasure ν]
      coordinateL1 u :=
    hcommonXm1.ae_eq (coeFn_toXm1Spatial u huM huXm1)
  have hx1Rep : toViscousX1Spatial ν u huM huX1 =ᵐ[commonFrequencyMeasure ν]
      coordinateL1 u :=
    hcommonX1.ae_eq (coeFn_toViscousX1Spatial ν u huM huX1)
  have hxmRestrict : xm1SpatialToCommon ν (toXm1Spatial u huM huXm1)
      =ᵐ[commonFrequencyMeasure ν] toXm1Spatial u huM huXm1 := by
    simpa [xm1SpatialToCommon] using
      (MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
        (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
        (by simpa using commonFrequencyMeasure_le_xm1 ν)
        (toXm1Spatial u huM huXm1))
  have hx1Restrict : viscousX1SpatialToCommon ν
      (toViscousX1Spatial ν u huM huX1) =ᵐ[commonFrequencyMeasure ν]
        toViscousX1Spatial ν u huM huX1 := by
    simpa [viscousX1SpatialToCommon] using
      (MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
        (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
        (by simpa using commonFrequencyMeasure_le_viscousX1 ν)
        (toViscousX1Spatial ν u huM huX1))
  filter_upwards [hxmRestrict, hx1Restrict, hxmRep, hx1Rep] with ξ hxr h1r hxu h1u
  rw [hxr, h1r, hxu, h1u]

section TimeLift

variable (u : ℝ → ES → ComplexSpace)
variable (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
variable (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
variable (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))

/-- The exact spatial `X⁻¹` representative of a raw time-frequency field. -/
def xm1Section (t : ℝ) : Xm1Spatial :=
  toXm1Spatial (u t) (huM t) (huXm1 t)

/-- The exact spatial viscous `X¹` representative of the same raw field. -/
def viscousX1Section (ν : ℝ≥0) (t : ℝ) : ViscousX1Spatial ν :=
  toViscousX1Spatial ν (u t) (huM t) (huX1 t)

theorem norm_xm1Section (t : ℝ) :
    ‖xm1Section u huM huXm1 t‖ = coordinateXm1Mass (u t) :=
  norm_toXm1Spatial (u t) (huM t) (huXm1 t)

theorem norm_viscousX1Section (ν : ℝ≥0) (t : ℝ) :
    ‖viscousX1Section u huM huX1 ν t‖ =
      (ν : ℝ) * coordinateX1Mass (u t) :=
  norm_toViscousX1Spatial ν (u t) (huM t) (huX1 t)

/-- A uniform `X⁻¹` budget and strong measurability in the actual spatial
quotient construct the finite-horizon essential-supremum slot. -/
def toXm1TimeSlot (T R : ℝ)
    (hTimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ R) :
    Xm1TimeSlot T :=
  (memLp_top_of_bound hTimeM R <| by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simpa [norm_xm1Section] using hR t ht).toLp (xm1Section u huM huXm1)

/-- The existing time-integrated coordinate `X¹` budget is exactly the
`MemLp 1` input for the viscosity-weighted spatial section. -/
theorem viscousX1Section_memLp_one (ν : ℝ≥0) (T : ℝ)
    (hTimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hX1 : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T)) :
    MemLp (viscousX1Section u huM huX1 ν) 1 (leiLinTimeMeasure T) := by
  have hnorm : Integrable (fun t => ‖viscousX1Section u huM huX1 ν t‖)
      (leiLinTimeMeasure T) := by
    apply (hX1.const_mul (ν : ℝ)).congr
    filter_upwards [] with t
    rw [norm_viscousX1Section]
  exact memLp_one_iff_integrable.mpr ((integrable_norm_iff hTimeM).mp hnorm)

/-- An integrated `X¹` budget and strong measurability in the actual spatial
quotient construct the finite-horizon viscous `X¹` slot. -/
def toViscousX1TimeSlot (ν : ℝ≥0) (T : ℝ)
    (hTimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hX1 : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T)) :
    ViscousX1TimeSlot ν T :=
  (viscousX1Section_memLp_one u huM huX1 ν T hTimeM hX1).toLp
    (viscousX1Section u huM huX1 ν)

theorem coeFn_toXm1TimeSlot (T R : ℝ)
    (hTimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ R) :
    toXm1TimeSlot u huM huXm1 T R hTimeM hR =ᵐ[leiLinTimeMeasure T]
      xm1Section u huM huXm1 := by
  exact MemLp.coeFn_toLp _

theorem coeFn_toViscousX1TimeSlot (ν : ℝ≥0) (T : ℝ)
    (hTimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hX1 : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T)) :
    toViscousX1TimeSlot u huM huX1 ν T hTimeM hX1 =ᵐ[leiLinTimeMeasure T]
      viscousX1Section u huM huX1 ν := by
  exact MemLp.coeFn_toLp _

end TimeLift

/-- The two independently completed time slots built from one raw spacetime
Fourier field have the same image in the common trajectory carrier.  This is
the compatibility proof required by `ActualLinkedCarrier`; it is derived from
the representatives and does not appear as an input hypothesis. -/
theorem realized_time_slots_eq_of_raw
    (ν : ℝ≥0) (T R : ℝ) (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))
    (hXm1TimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hX1TimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hXm1Bound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ R)
    (hX1Int : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T)) :
    realizeXm1Trajectory ν T
        (toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound) =
      realizeViscousX1Trajectory ν T
        (toViscousX1TimeSlot u huM huX1 ν T hX1TimeM hX1Int) := by
  let μ := leiLinTimeMeasure T
  let xm := toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound
  let x1 := toViscousX1TimeSlot u huM huX1 ν T hX1TimeM hX1Int
  let xmCommonTop := (xm1SpatialToCommon ν).compLpL ∞ μ xm
  have hxmOuter : Filter.EventuallyEq (ae μ)
      (fun t => ((lpTopToLpOne μ xmCommonTop : Lp (CommonSpatial ν) 1 μ) :
        ℝ → CommonSpatial ν) t)
      (fun t => ((xmCommonTop : Lp (CommonSpatial ν) ∞ μ) :
        ℝ → CommonSpatial ν) t) := by
    filter_upwards [] with t
    rfl
  have hxmInner : Filter.EventuallyEq (ae μ)
      (fun t => ((xmCommonTop : Lp (CommonSpatial ν) ∞ μ) :
        ℝ → CommonSpatial ν) t)
      (fun t => xm1SpatialToCommon ν (((xm : Xm1TimeSlot T) : ℝ → Xm1Spatial) t)) := by
    exact (xm1SpatialToCommon ν).coeFn_compLpL xm
  have hx1Inner : Filter.EventuallyEq (ae μ)
      (fun t => ((((viscousX1SpatialToCommon ν).compLpL 1 μ x1 :
        CommonTrajectorySlot ν T)) : ℝ → CommonSpatial ν) t)
      (fun t => viscousX1SpatialToCommon ν
        (((x1 : ViscousX1TimeSlot ν T) : ℝ → ViscousX1Spatial ν) t)) := by
    exact (viscousX1SpatialToCommon ν).coeFn_compLpL x1
  have hxmRep : Filter.EventuallyEq (ae μ)
      (fun t => (((xm : Xm1TimeSlot T) : ℝ → Xm1Spatial) t))
      (xm1Section u huM huXm1) := by
    simpa [μ, xm] using
      coeFn_toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound
  have hx1Rep : Filter.EventuallyEq (ae μ)
      (fun t => (((x1 : ViscousX1TimeSlot ν T) : ℝ → ViscousX1Spatial ν) t))
      (viscousX1Section u huM huX1 ν) := by
    simpa [μ, x1] using
      coeFn_toViscousX1TimeSlot u huM huX1 ν T hX1TimeM hX1Int
  apply Lp.ext
  filter_upwards [hxmOuter, hxmInner, hx1Inner, hxmRep, hx1Rep] with
    t hxo hxi h1i hxr h1r
  rw [show realizeXm1Trajectory ν T
      (toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound) =
        lpTopToLpOne μ xmCommonTop by rfl,
    show realizeViscousX1Trajectory ν T
      (toViscousX1TimeSlot u huM huX1 ν T hX1TimeM hX1Int) =
        (viscousX1SpatialToCommon ν).compLpL 1 μ x1 by rfl]
  rw [hxo, hxi, h1i, hxr, h1r]
  exact spatial_realizations_eq ν (u t) (huM t) (huXm1 t) (huX1 t)

/-- A raw spacetime Fourier field with the established Lei--Lin budgets gives
an element of the exact linked Banach carrier.  Equality of the two coordinate
representatives is proved above from their common raw field. -/
def actualLinkedOfRaw
    (ν : ℝ≥0) (T R : ℝ) (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))
    (hXm1TimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hX1TimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hXm1Bound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ R)
    (hX1Int : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T)) :
    ActualLinkedCarrier ν T :=
  ⟨WithLp.toLp 1
      (toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound,
        toViscousX1TimeSlot u huM huX1 ν T hX1TimeM hX1Int),
    realized_time_slots_eq_of_raw ν T R u huM huXm1 huX1
      hXm1TimeM hX1TimeM hXm1Bound hX1Int⟩

/-- The actual continuous mild image enters the concrete linked carrier once
its already-proved pointwise `X⁻¹` and time-integrated `X¹` budgets are paired
with spatial integrability and time strong measurability.  No fixed point or
self-map proposition is assumed. -/
def actualLinkedContinuousMildImage
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (hM : ∀ t i, AEStronglyMeasurable (fun ξ =>
      ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i) volume)
    (hXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i‖))
    (hX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ *
      ‖ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i‖))
    (hXm1TimeM : AEStronglyMeasurable
      (xm1Section
        (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a v)
        hM hXm1) (leiLinTimeMeasure T))
    (hX1TimeM : AEStronglyMeasurable
      (viscousX1Section
        (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a v)
        hM hX1 ν) (leiLinTimeMeasure T))
    (hXm1Bound : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass
        (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
          a v t) ≤ R)
    (hX1Int : Integrable (fun t => coordinateX1Mass
      (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t)) (leiLinTimeMeasure T)) :
    ActualLinkedCarrier ν T :=
  actualLinkedOfRaw ν T R
    (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a v)
    hM hXm1 hX1 hXm1TimeM hX1TimeM hXm1Bound hX1Int


end Navier.Analysis.ContinuousLeiLinTrajectoryLift

#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.coordinateL1_xm1_integrable
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.coordinateL1_viscousX1_integrable
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.norm_toXm1Spatial
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.norm_toViscousX1Spatial
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.spatial_realizations_eq
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.viscousX1Section_memLp_one
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.realized_time_slots_eq_of_raw
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryLift.actualLinkedContinuousMildImage
