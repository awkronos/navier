import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Navier.Analysis.ContinuousLeiLinLinkedComplete

/-!
# Concrete Banach slots for the continuous Lei--Lin trajectory

For a finite horizon `T`, this file instantiates the two abstract slots of
`ContinuousLeiLinLinkedComplete` as the actual nested Bochner spaces

* `L∞([0,T]; L¹(|ξ|⁻¹ dξ; ℓ¹(Fin 3; ℂ)))`, and
* `L¹([0,T]; L¹(ν|ξ| dξ; ℓ¹(Fin 3; ℂ)))`.

Putting `ν` into the second frequency measure makes its norm exactly the
viscosity-weighted dissipation slot.  The finite coordinate `PiLp 1` norm is
the sum of the three component norms, matching `coordinateXm1Mass` and
`coordinateX1Mass` rather than the Euclidean pointwise norm.

Both slots map into `L¹` in time and frequency for the common density
`min (|ξ|⁻¹) (ν|ξ|)`.  This density is positive away from the singleton
`ξ = 0` when `ν > 0`, so its measure has the same null sets as Lebesgue
measure.  The common realization therefore records the actual spacetime
Fourier trajectory up to the physically relevant a.e. relation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinLinkedComplete

namespace Navier.Analysis.ContinuousLeiLinActualSlots

/-- The pointwise `ℓ¹` norm over the three Fourier coordinates. -/
abbrev FourierCoordinateL1 := PiLp 1 (fun _ : Fin 3 => ℂ)

/-- Lebesgue time measure restricted to the finite iteration horizon. -/
def leiLinTimeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) T)

instance leiLinTimeMeasureIsFinite (T : ℝ) :
    IsFiniteMeasure (leiLinTimeMeasure T) := by
  dsimp [leiLinTimeMeasure]
  infer_instance

/-- The homogeneous `X⁻¹` frequency density. -/
def xm1Density (ξ : ES) : ℝ≥0∞ :=
  ENNReal.ofReal ‖ξ‖⁻¹

/-- The viscosity-weighted `X¹` frequency density. -/
def viscousX1Density (ν : ℝ≥0) (ξ : ES) : ℝ≥0∞ :=
  (ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖

/-- A common positive-a.e. density dominated by both Lei--Lin weights. -/
def commonFrequencyDensity (ν : ℝ≥0) (ξ : ES) : ℝ≥0∞ :=
  min (xm1Density ξ) (viscousX1Density ν ξ)

def xm1FrequencyMeasure : Measure ES :=
  volume.withDensity xm1Density

def viscousX1FrequencyMeasure (ν : ℝ≥0) : Measure ES :=
  volume.withDensity (viscousX1Density ν)

def commonFrequencyMeasure (ν : ℝ≥0) : Measure ES :=
  volume.withDensity (commonFrequencyDensity ν)

/-- Measurability of the common density. -/
theorem commonFrequencyDensity_measurable (ν : ℝ≥0) :
    Measurable (commonFrequencyDensity ν) := by
  apply Measurable.min
  · exact ENNReal.measurable_ofReal.comp measurable_norm.inv
  · exact measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_norm)

/-- For positive viscosity, the common density vanishes only at the
Lebesgue-null zero frequency. -/
theorem commonFrequencyDensity_ne_zero_ae (ν : ℝ≥0) (hν : 0 < ν) :
    ∀ᵐ ξ : ES ∂volume, commonFrequencyDensity ν ξ ≠ 0 := by
  have hzero : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with ξ hξ
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hXm1 : 0 < xm1Density ξ := by
    simp [xm1Density, ENNReal.ofReal_pos, inv_pos.mpr hnorm]
  have hX1 : 0 < viscousX1Density ν ξ := by
    have hνE : (0 : ℝ≥0∞) < (ν : ℝ≥0∞) := by exact_mod_cast hν
    have hnormE : (0 : ℝ≥0∞) < ENNReal.ofReal ‖ξ‖ :=
      ENNReal.ofReal_pos.mpr hnorm
    exact ENNReal.mul_pos hνE.ne' hnormE.ne'
  exact (lt_min hXm1 hX1).ne'

/-- The common frequency measure has every Lebesgue-null set and, at positive
viscosity, no additional null sets. -/
theorem volume_absolutelyContinuous_commonFrequencyMeasure
    (ν : ℝ≥0) (hν : 0 < ν) :
    volume ≪ commonFrequencyMeasure ν := by
  exact withDensity_absolutelyContinuous'
    (commonFrequencyDensity_measurable ν).aemeasurable
    (commonFrequencyDensity_ne_zero_ae ν hν)

/-- Equality in the common carrier implies equality in the `X⁻¹` carrier. -/
theorem xm1FrequencyMeasure_absolutelyContinuous_common
    (ν : ℝ≥0) (hν : 0 < ν) :
    xm1FrequencyMeasure ≪ commonFrequencyMeasure ν :=
  (withDensity_absolutelyContinuous volume xm1Density).trans
    (volume_absolutelyContinuous_commonFrequencyMeasure ν hν)

/-- Equality in the common carrier implies equality in the viscous `X¹`
carrier. -/
theorem viscousX1FrequencyMeasure_absolutelyContinuous_common
    (ν : ℝ≥0) (hν : 0 < ν) :
    viscousX1FrequencyMeasure ν ≪ commonFrequencyMeasure ν :=
  (withDensity_absolutelyContinuous volume (viscousX1Density ν)).trans
    (volume_absolutelyContinuous_commonFrequencyMeasure ν hν)

/-- The spatial `X⁻¹` Banach space with coordinate-sum norm. -/
abbrev Xm1Spatial := Lp FourierCoordinateL1 1 xm1FrequencyMeasure

/-- The spatial `νX¹` Banach space with coordinate-sum norm. -/
abbrev ViscousX1Spatial (ν : ℝ≥0) :=
  Lp FourierCoordinateL1 1 (viscousX1FrequencyMeasure ν)

/-- The common spatial `L¹` carrier used to compare the two representatives. -/
abbrev CommonSpatial (ν : ℝ≥0) :=
  Lp FourierCoordinateL1 1 (commonFrequencyMeasure ν)

/-- The actual time-essential-supremum `X⁻¹` slot. -/
abbrev Xm1TimeSlot (T : ℝ) :=
  Lp Xm1Spatial ∞ (leiLinTimeMeasure T)

/-- The actual time-integrated viscosity-weighted `X¹` slot. -/
abbrev ViscousX1TimeSlot (ν : ℝ≥0) (T : ℝ) :=
  Lp (ViscousX1Spatial ν) 1 (leiLinTimeMeasure T)

/-- A common `L¹` spacetime trajectory carrier. -/
abbrev CommonTrajectorySlot (ν : ℝ≥0) (T : ℝ) :=
  Lp (CommonSpatial ν) 1 (leiLinTimeMeasure T)

/-- The common frequency measure is dominated by the `X⁻¹` measure. -/
theorem commonFrequencyMeasure_le_xm1 (ν : ℝ≥0) :
    commonFrequencyMeasure ν ≤ xm1FrequencyMeasure := by
  apply withDensity_mono
  exact Eventually.of_forall fun ξ => min_le_left _ _

/-- The common frequency measure is dominated by the viscous `X¹` measure. -/
theorem commonFrequencyMeasure_le_viscousX1 (ν : ℝ≥0) :
    commonFrequencyMeasure ν ≤ viscousX1FrequencyMeasure ν := by
  apply withDensity_mono
  exact Eventually.of_forall fun ξ => min_le_right _ _

/-- Restriction of an `X⁻¹` representative to the common positive-a.e. measure. -/
def xm1SpatialToCommon (ν : ℝ≥0) : Xm1Spatial →L[ℝ] CommonSpatial ν :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonFrequencyMeasure_le_xm1 ν)

/-- Restriction of a viscous `X¹` representative to the common measure. -/
def viscousX1SpatialToCommon (ν : ℝ≥0) :
    ViscousX1Spatial ν →L[ℝ] CommonSpatial ν :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonFrequencyMeasure_le_viscousX1 ν)

/-- The common-measure restriction loses no `X⁻¹` representative when
`ν > 0`, because the original weighted measure is absolutely continuous with
respect to the common measure. -/
theorem xm1SpatialToCommon_injective (ν : ℝ≥0) (hν : 0 < ν) :
    Function.Injective (xm1SpatialToCommon ν) := by
  intro f g hfg
  apply Lp.ext
  apply (xm1FrequencyMeasure_absolutelyContinuous_common ν hν).ae_eq
  have hf : xm1SpatialToCommon ν f =ᵐ[commonFrequencyMeasure ν] f := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_xm1 ν) f
  have hg : xm1SpatialToCommon ν g =ᵐ[commonFrequencyMeasure ν] g := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_xm1 ν) g
  filter_upwards [hf, hg] with ξ hfξ hgξ
  rw [← hfξ, ← hgξ, hfg]

/-- The common-measure restriction also loses no viscous `X¹`
representative at positive viscosity. -/
theorem viscousX1SpatialToCommon_injective (ν : ℝ≥0) (hν : 0 < ν) :
    Function.Injective (viscousX1SpatialToCommon ν) := by
  intro f g hfg
  apply Lp.ext
  apply (viscousX1FrequencyMeasure_absolutelyContinuous_common ν hν).ae_eq
  have hf : viscousX1SpatialToCommon ν f =ᵐ[commonFrequencyMeasure ν] f := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_viscousX1 ν) f
  have hg : viscousX1SpatialToCommon ν g =ᵐ[commonFrequencyMeasure ν] g := by
    exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa using commonFrequencyMeasure_le_viscousX1 ν) g
  filter_upwards [hf, hg] with ξ hfξ hgξ
  rw [← hfξ, ← hgξ, hfg]

section FiniteTimeInclusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- The algebraic inclusion `L∞(μ; E) → L¹(μ; E)` on a finite measure. -/
def lpTopToLpOneLinear : Lp E ∞ μ →ₗ[ℝ] Lp E 1 μ where
  toFun f := ⟨f.1, Lp.antitone (p := (1 : ℝ≥0∞)) (q := ∞) (by simp) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite-measure `L∞ → L¹` inclusion is bounded by `μ univ`. -/
theorem norm_lpTopToLpOneLinear_le (f : Lp E ∞ μ) :
    ‖lpTopToLpOneLinear μ f‖ ≤ (μ univ).toReal * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  change (eLpNorm (f : ℝ → E) 1 μ).toReal ≤
    (μ univ).toReal * (eLpNorm (f : ℝ → E) ∞ μ).toReal
  have hμtop : μ univ ≠ ∞ := measure_ne_top μ univ
  have hfTop : eLpNorm (f : ℝ → E) ∞ μ ≠ ∞ := Lp.eLpNorm_ne_top f
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := (f : ℝ → E)) (p := (1 : ℝ≥0∞)) (q := ∞)
    (by simp) (f : ℝ →ₘ[μ] E).aestronglyMeasurable
  have hbound' : eLpNorm (f : ℝ → E) 1 μ ≤
      eLpNorm (f : ℝ → E) ∞ μ * μ univ := by
    simpa using hbound
  simpa [ENNReal.toReal_mul, mul_comm] using
    (ENNReal.toReal_mono (ENNReal.mul_ne_top hfTop hμtop) hbound')

/-- Continuous finite-horizon realization of an essential-supremum trajectory
as an integrable trajectory. -/
def lpTopToLpOne : Lp E ∞ μ →L[ℝ] Lp E 1 μ :=
  LinearMap.mkContinuous (lpTopToLpOneLinear μ) (μ univ).toReal
    (norm_lpTopToLpOneLinear_le μ)

/-- The finite-time `L∞ → L¹` inclusion retains the same a.e. representative. -/
theorem lpTopToLpOne_injective :
    Function.Injective (lpTopToLpOne (E := E) μ) := by
  intro f g hfg
  apply Subtype.ext
  exact congrArg (fun q : Lp E 1 μ => q.1) hfg

end FiniteTimeInclusion

section PointwiseRealization

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Applying an injective continuous linear map pointwise gives an injective
map on every Bochner `Lᵖ` space. -/
theorem compLpL_injective (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure ℝ)
    (L : E →L[ℝ] F) (hL : Function.Injective L) :
    Function.Injective (L.compLpL p μ) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL f, L.coeFn_compLpL g] with t hft hgt
  apply hL
  rw [← hft, ← hgt, hfg]

end PointwiseRealization

/-- Realization of the `X⁻¹` time-essential-supremum slot in the common
spacetime `L¹` carrier. -/
def realizeXm1Trajectory (ν : ℝ≥0) (T : ℝ) :
    Xm1TimeSlot T →L[ℝ] CommonTrajectorySlot ν T :=
  (lpTopToLpOne (E := CommonSpatial ν) (leiLinTimeMeasure T)).comp
    ((xm1SpatialToCommon ν).compLpL ∞ (leiLinTimeMeasure T))

/-- Realization of the time-integrated viscous `X¹` slot in the same common
spacetime `L¹` carrier. -/
def realizeViscousX1Trajectory (ν : ℝ≥0) (T : ℝ) :
    ViscousX1TimeSlot ν T →L[ℝ] CommonTrajectorySlot ν T :=
  (viscousX1SpatialToCommon ν).compLpL 1 (leiLinTimeMeasure T)

/-- Positive viscosity makes the `X⁻¹` realization faithful. -/
theorem realizeXm1Trajectory_injective (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) :
    Function.Injective (realizeXm1Trajectory ν T) :=
  lpTopToLpOne_injective (E := CommonSpatial ν) (leiLinTimeMeasure T) |>.comp
    (compLpL_injective ∞ (leiLinTimeMeasure T) (xm1SpatialToCommon ν)
      (xm1SpatialToCommon_injective ν hν))

/-- Positive viscosity makes the `X¹` realization faithful. -/
theorem realizeViscousX1Trajectory_injective
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) :
    Function.Injective (realizeViscousX1Trajectory ν T) :=
  compLpL_injective 1 (leiLinTimeMeasure T) (viscousX1SpatialToCommon ν)
    (viscousX1SpatialToCommon_injective ν hν)

/-- The concrete linked Lei--Lin trajectory carrier on `[0,T]`. -/
abbrev ActualLinkedCarrier (ν : ℝ≥0) (T : ℝ) :=
  LinkedAdmissibleCarrier (realizeXm1Trajectory ν T)
    (realizeViscousX1Trajectory ν T)

/-- The concrete coordinatewise admissible box on `[0,T]`. -/
abbrev ActualLinkedBox (ν : ℝ≥0) (T xm1Radius x1WeightedRadius : ℝ) :=
  LinkedAdmissibleBox (realizeXm1Trajectory ν T)
    (realizeViscousX1Trajectory ν T) xm1Radius x1WeightedRadius

/-- The actual linked trajectory carrier is complete. -/
theorem actualLinkedCarrier_complete (ν : ℝ≥0) (T : ℝ) :
    CompleteSpace (ActualLinkedCarrier ν T) := by
  infer_instance

/-- The actual coordinatewise admissible box is complete. -/
theorem actualLinkedBox_complete (ν : ℝ≥0) (T xm1Radius x1WeightedRadius : ℝ) :
    CompleteSpace (ActualLinkedBox ν T xm1Radius x1WeightedRadius) := by
  infer_instance

/-- Banach's theorem on the concrete Lei--Lin trajectory box.  The only
operator input is the coordinate sum estimate already supplied analytically
for the mild map; completeness and common-trajectory linkage are discharged
by the concrete spaces above. -/
theorem actual_existsUnique_fixedPoint_of_coordinate_sum
    (ν : ℝ≥0) (T xm1Radius x1WeightedRadius : ℝ)
    (hxm1Radius : 0 ≤ xm1Radius)
    (hx1WeightedRadius : 0 ≤ x1WeightedRadius)
    (Φ : ActualLinkedBox ν T xm1Radius x1WeightedRadius →
      ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (K : ℝ≥0) (hK : K < 1)
    (hΦ : ∀ u v,
      dist (Φ u).1.1.fst (Φ v).1.1.fst +
          dist (Φ u).1.1.snd (Φ v).1.1.snd ≤
        (K : ℝ) * (dist u.1.1.fst v.1.1.fst +
          dist u.1.1.snd v.1.1.snd)) :
    ∃ x, Φ x = x ∧ ∀ y, Φ y = y → y = x := by
  exact existsUnique_fixedPoint_of_coordinate_sum
    (realizeXm1Trajectory ν T) (realizeViscousX1Trajectory ν T)
    xm1Radius x1WeightedRadius hxm1Radius hx1WeightedRadius Φ K hK hΦ

end Navier.Analysis.ContinuousLeiLinActualSlots

#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.commonFrequencyMeasure_le_xm1
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.volume_absolutelyContinuous_commonFrequencyMeasure
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.norm_lpTopToLpOneLinear_le
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.realizeXm1Trajectory_injective
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.realizeViscousX1Trajectory_injective
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.actualLinkedCarrier_complete
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.actualLinkedBox_complete
#print axioms Navier.Analysis.ContinuousLeiLinActualSlots.actual_existsUnique_fixedPoint_of_coordinate_sum
