import Navier.Analysis.ContinuousLeiLinActualSlots
import Navier.Analysis.ContinuousLeiLinCommonRepresentative
import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
import Navier.Analysis.ContinuousLeiLinTrajectoryLift
import Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability
import Navier.Analysis.ContinuousLeiLinRecentTailInputs
import Navier.Analysis.WholeSpaceRestartX2BudgetWiring

/-!
# Pattern-A carrier change: a weight-degree-2 slot in the restart box

## Why this module exists (the falsification it answers)

`Navier/Analysis/MildHorizonFreeRestartBarrier.lean` (lane W31-N02) proves
`exists_slots_below_radii_hv2_fails`: for every pair of radii `B1, B2 > 0`
there is a Fourier trajectory whose `X⁻¹` and `X¹` coordinate masses stay
below `B1` and `B2` while the degree-2 leg `hv2` fails.  That is a
kernel-checked refutation of the route "the budget legs `hv2` / `hX2` /
`hbdd` of `WholeSpaceRestartX2BudgetWiring.SourceX2Budget` are functions of
the two box radii".  The obstruction is a data-width mismatch of the record:
the box `ActualLinkedBox ν T B1 B2` carries the slots
`Xm1TimeSlot T = L∞_t(L¹(‖ξ‖⁻¹ dξ))` and
`ViscousX1TimeSlot ν T = L¹_t(L¹(ν‖ξ‖ dξ))`, and the weight `‖ξ‖²` dominates
neither slot density at the ultraviolet end, so degree-2 mass is inexpressible
in the degree-1 record.

## What this module adds

A third slot of weight degree 2, `X2TimeSlot T = L∞_t(L¹(‖ξ‖² dξ))`, an
extended linkage carrier `CommonSpatialX2 ν` whose density
`min (common density) ‖ξ‖²` is dominated by all three slot densities, and the
extended box record `ActualLinkedBoxX2 ν T B1 B2 B3`: an actual linked box
together with an `L∞_t X²` slot realized, in the extended common trajectory
carrier, to the SAME spacetime trajectory as the `X⁻¹` slot.  The slot is a
CONSTRUCTED object: the constant Fourier-datum trajectory (`boxX2Constant`,
all degree-2 moments finite by Schwartz decay) and the zero trajectory
(`boxX2Zero`) inhabit concrete extended boxes with explicit radii.  Nothing
here asserts existence of a slot by declaration alone.

## What the extended record DETERMINES (vs N02's falsification)

For `b : ActualLinkedBoxX2 ν T B1 B2 B3`, the gated raw field
`boxX2RawRepresentative ν T B1 B2 B3 b` satisfies, at EVERY time:

* `boxX2_hv2` — per-time degree-2 coordinate integrability `hv2`;
* `boxX2_hbdd` — the uniform `X⁰` mass bound `B1 + B3` (the pointwise split
  `‖f‖ ≤ ‖ξ‖⁻¹‖f‖` on `‖ξ‖ ≤ 1`, `‖f‖ ≤ ‖ξ‖²‖f‖` on `1 < ‖ξ‖`, which the
  degree-1 record could not make uniform because its `X¹` slot is `L¹_t`);
* `boxX2_hX2` — time-integrability of the degree-2 moment mass;
* `boxX2_hv0` — per-time unweighted coordinate integrability.

Together these are the four non-continuity legs of the provider
`ContinuousLeiLinSourceX1MomentBound.sourceL1X1_of_continuous_uniformX0_integrableX2`;
the fifth, joint continuity `hv`, is a regularity of the representative, not a
radius datum.  `boxX2_sourceL1X1` consumes the provider: given `hv` for the
gated field, `SourceL1X1 T (boxX2RawRepresentative ν T B1 B2 B3 b)` holds —
the restart premise shape, now read off three numbers `(B1, B2, B3)` plus the
linkage.

## The falsification STILL STANDS

`exists_slots_below_radii_hv2_fails` refutes determination from the
**degree-1 class**: from `(B1, B2)` alone, with no degree-2 datum, no
function of the two radii bounds `hv2`.  Adding the `B3` slot does not undo
it: the barrier trajectory's degree-2 coordinate mass is `⊤`
(barrier_X2_lintegral_eq_top in the barrier file), so it lies in NO extended
box `ActualLinkedBoxX2 ν T B1 B2 B3` for any finite `B3`.  The new slot is a
genuine extra input, not a re-encoding of `B1, B2`.  What changed is exactly
the determination question: before this module the ultraviolet degree-2 datum
was absent from the record; now membership in the extended box carries it.

## Honest scope

* This module does NOT prove the mild self-map preserves the extended box
  (the analytic degree-2 Duhamel output estimate — the true crown leg,
  sibling of the `s^{−1/2}` wall in `ContinuousLeiLinMildAssemblyLeaves`).
  It does NOT touch the smallness field `restartRadius u₀ ≤ ν / 16`.
* `boxX2RawRepresentative` and the crown's `everywhereRawRepresentative`
  agree at almost every time (`boxX2RawRepresentative_eq_everywhere_ae`);
  transferring `SourceL1X1` across that time-null set needs a.e.-stability
  of the convolution source, which is NOT proved here — the statement is
  given at the gated field itself.
* The whole-space global regularity crown stays OPEN.  Nothing in this file
  closes a crown.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinLinkedComplete
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRecentTailInputs
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.WholeSpaceRestartX2BudgetWiring

open scoped FourierTransform SchwartzMap
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)
open Navier.Analysis.FourierMajorant (euclidComponent)

namespace Navier.Analysis.LinkedBoxX2Carrier

/-! ## The degree-2 frequency data -/

/-- The homogeneous weight-degree-2 frequency density. -/
def x2Density (ξ : ES) : ENNReal := ENNReal.ofReal (‖ξ‖ ^ 2)

/-- The weight-degree-2 frequency measure. -/
def x2FrequencyMeasure : Measure ES := volume.withDensity x2Density

theorem x2Density_measurable : Measurable x2Density :=
  ENNReal.measurable_ofReal.comp (measurable_norm.pow (measurable_const))

theorem x2Density_toReal (ξ : ES) : (x2Density ξ).toReal = ‖ξ‖ ^ 2 :=
  ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg ξ) 2)

theorem x2Density_ne_zero_ae : ∀ᵐ ξ : ES ∂volume, x2Density ξ ≠ 0 := by
  have hzero : ∀ᵐ ξ : ES ∂volume, ξ ≠ (0 : ES) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with ξ hξ
  have hpos : (0 : ℝ) < ‖(ξ : ES)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξ) 2
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-- The spatial `X²` Banach space: `L¹` of the degree-2 weighted measure with
the coordinate-sum norm. -/
abbrev X2Spatial := Lp FourierCoordinateL1 1 x2FrequencyMeasure

/-- The time-essential-supremum `X²` slot: `L∞_t X²Spatial`. -/
abbrev X2TimeSlot (T : ℝ) := Lp X2Spatial ∞ (leiLinTimeMeasure T)

/-! ### Construction from a raw field (mirrors `toViscousX1Spatial`) -/

theorem coordinateL1_x2_integrable (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    Integrable (coordinateL1 u) x2FrequencyMeasure := by
  change Integrable (coordinateL1 u)
    (volume.withDensity (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ 2)))
  refine (integrable_withDensity_iff_integrable_smul'
    (μ := volume) (g := coordinateL1 u)
    x2Density_measurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2 ?_
  change Integrable
    (fun ξ : ES => (ENNReal.ofReal (‖ξ‖ ^ 2)).toReal • coordinateL1 u ξ) volume
  have hvM : AEStronglyMeasurable (coordinateL1 u) volume :=
    coordinateL1_aestronglyMeasurable u huM
  have hdM : AEStronglyMeasurable
      (fun ξ : ES => (ENNReal.ofReal (‖ξ‖ ^ 2)).toReal) volume :=
    (x2Density_measurable.ennreal_toReal).aestronglyMeasurable
  have hweightedM : AEStronglyMeasurable
      (fun ξ : ES => (ENNReal.ofReal (‖ξ‖ ^ 2)).toReal • coordinateL1 u ξ) volume :=
    hdM.smul hvM
  apply (integrable_norm_iff hweightedM).mp
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ‖ξ‖ ^ 2 * ‖u ξ i‖) :=
    integrable_finsetSum Finset.univ (fun i _ => huI i)
  apply hsum.congr
  filter_upwards [] with ξ
  rw [norm_smul, ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg ξ) 2),
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg ξ) 2),
    norm_coordinateL1, Finset.mul_sum]

/-- Build the spatial `X²` quotient from a raw Fourier field with finite
degree-2 weighted coordinates. -/
def toX2Spatial (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    X2Spatial :=
  (memLp_one_iff_integrable.mpr (coordinateL1_x2_integrable u huM huI)).toLp
    (coordinateL1 u)

theorem coeFn_toX2Spatial (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    toX2Spatial u huM huI =ᵐ[x2FrequencyMeasure] coordinateL1 u :=
  MemLp.coeFn_toLp _

/-- The spatial `X²` norm of a raw field's quotient is exactly the degree-2
coordinate moment mass. -/
theorem norm_toX2Spatial
    (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    ‖toX2Spatial u huM huI‖ = coordinateMomentMass 2 u := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ ξ : ES, ‖coordinateL1 u ξ‖ ∂x2FrequencyMeasure :=
      integral_congr_ae <| by
        filter_upwards [coeFn_toX2Spatial u huM huI] with ξ hξ
        rw [hξ]
    _ = coordinateMomentMass 2 u := by
      change (∫ ξ : ES, ‖coordinateL1 u ξ‖
        ∂volume.withDensity (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ 2))) = _
      calc
        _ = ∫ ξ : ES, (ENNReal.ofReal (‖ξ‖ ^ 2)).toReal •
            ‖coordinateL1 u ξ‖ ∂volume := by
          exact integral_withDensity_eq_integral_toReal_smul
            (μ := volume) (g := fun ξ : ES => ‖coordinateL1 u ξ‖)
            x2Density_measurable
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
        _ = coordinateMomentMass 2 u := by
          unfold coordinateMomentMass
          calc
            _ = ∫ ξ : ES, ∑ i : Fin 3, ‖ξ‖ ^ 2 * ‖u ξ i‖ := by
              apply integral_congr_ae
              filter_upwards [] with ξ
              rw [norm_coordinateL1]
              change (ENNReal.ofReal (‖ξ‖ ^ 2)).toReal * ∑ i : Fin 3, ‖u ξ i‖ = _
              rw [ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg ξ) 2),
                Finset.mul_sum]
            _ = ∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖u ξ i‖ :=
              integral_finsetSum Finset.univ (fun i _ => huI i)

/-- Every element of the spatial `X²` quotient has integrable raw coordinates
against the literal degree-2 weight (mirrors `xm1Spatial_integrable_coordinate`). -/
theorem x2Spatial_integrable_coordinate (f : X2Spatial) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖(f ξ : FourierCoordinateL1).ofLp i‖) := by
  have hf : Integrable (fun ξ : ES => (f ξ : FourierCoordinateL1))
      x2FrequencyMeasure :=
    memLp_one_iff_integrable.mp (Lp.memLp f)
  have hsmul : Integrable (fun ξ : ES =>
      (x2Density ξ).toReal • (f ξ : FourierCoordinateL1)) volume :=
    (integrable_withDensity_iff_integrable_smul'
      x2Density_measurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hf
  have hi : Integrable (fun ξ : ES =>
      ((x2Density ξ).toReal • (f ξ : FourierCoordinateL1)) i) volume :=
    hsmul.eval_piLp i
  apply hi.norm.congr
  filter_upwards [] with ξ
  change ‖(x2Density ξ).toReal • (f ξ : FourierCoordinateL1).ofLp i‖ = _
  rw [norm_smul, x2Density_toReal]
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg ξ) 2)]

/-- The degree-2 norm identity for an arbitrary quotient element: its spatial
norm is the degree-2 moment mass of its raw coordinate field. -/
theorem norm_x2Spatial_eq (f : X2Spatial) :
    ‖f‖ = coordinateMomentMass 2 (fun ξ : ES => (f ξ : FourierCoordinateL1).ofLp) := by
  rw [L1.norm_eq_integral_norm]
  change (∫ ξ : ES, ‖(f ξ : FourierCoordinateL1)‖ ∂x2FrequencyMeasure) = _
  calc
    _ = ∫ ξ : ES, (x2Density ξ).toReal • ‖(f ξ : FourierCoordinateL1)‖ ∂volume := by
      exact integral_withDensity_eq_integral_toReal_smul
        (μ := volume) (g := fun ξ : ES => ‖(f ξ : FourierCoordinateL1)‖)
        x2Density_measurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    _ = coordinateMomentMass 2 (fun ξ : ES => (f ξ : FourierCoordinateL1).ofLp) := by
      unfold coordinateMomentMass
      calc
        _ = ∫ ξ : ES, ∑ i : Fin 3, ‖ξ‖ ^ 2 *
            ‖(f ξ : FourierCoordinateL1).ofLp i‖ ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with ξ
          rw [x2Density_toReal, smul_eq_mul, PiLp.norm_eq_of_L1, Finset.mul_sum]
        _ = ∑ i : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 *
            ‖(f ξ : FourierCoordinateL1).ofLp i‖ ∂volume :=
          integral_finsetSum Finset.univ
            (fun i _ => x2Spatial_integrable_coordinate f i)

/-! ## The extended linkage carrier: density dominated by all three slots -/

/-- The density `min (common density) ‖ξ‖²` of the carrier that receives the
`X⁻¹` and `X²` spatial quotients simultaneously (it is also dominated by the
viscous `X¹` density through the common density). -/
def commonX2FrequencyDensity (ν : ℝ≥0) (ξ : ES) : ENNReal :=
  min (commonFrequencyDensity ν ξ) (x2Density ξ)

/-- The extended common frequency measure. -/
def commonX2FrequencyMeasure (ν : ℝ≥0) : Measure ES :=
  volume.withDensity (commonX2FrequencyDensity ν)

/-- The spatial carrier receiving all three slots. -/
abbrev CommonSpatialX2 (ν : ℝ≥0) :=
  Lp FourierCoordinateL1 1 (commonX2FrequencyMeasure ν)

/-- The common spacetime `L¹` carrier for the extended box. -/
abbrev CommonTrajectorySlotX2 (ν : ℝ≥0) (T : ℝ) :=
  Lp (CommonSpatialX2 ν) 1 (leiLinTimeMeasure T)

theorem commonX2FrequencyDensity_measurable (ν : ℝ≥0) :
    Measurable (commonX2FrequencyDensity ν) := by
  unfold commonX2FrequencyDensity
  exact (commonFrequencyDensity_measurable ν).min x2Density_measurable

theorem commonX2FrequencyDensity_ne_zero_ae (ν : ℝ≥0) (hν : 0 < ν) :
    ∀ᵐ ξ : ES ∂volume, commonX2FrequencyDensity ν ξ ≠ 0 := by
  filter_upwards [commonFrequencyDensity_ne_zero_ae ν hν, x2Density_ne_zero_ae]
    with ξ h1 h2
  simp only [commonX2FrequencyDensity]
  have p1 : (0 : ENNReal) < commonFrequencyDensity ν ξ :=
    lt_of_le_of_ne zero_le (Ne.symm h1)
  have p2 : (0 : ENNReal) < x2Density ξ :=
    lt_of_le_of_ne zero_le (Ne.symm h2)
  exact (lt_min p1 p2).ne'

/-- Lebesgue-null sets are `commonX2`-null. -/
theorem volume_absolutelyContinuous_commonX2FrequencyMeasure
    (ν : ℝ≥0) (hν : 0 < ν) :
    volume ≪ commonX2FrequencyMeasure ν :=
  withDensity_absolutelyContinuous'
    (commonX2FrequencyDensity_measurable ν).aemeasurable
    (commonX2FrequencyDensity_ne_zero_ae ν hν)

/-- The extended common density is dominated by the degree-2 density. -/
theorem commonX2FrequencyMeasure_le_x2 (ν : ℝ≥0) :
    commonX2FrequencyMeasure ν ≤ x2FrequencyMeasure := by
  apply withDensity_mono
  exact Eventually.of_forall fun ξ => min_le_right _ _

/-- The extended common density is dominated by the common density, hence by
each of the two original slot densities. -/
theorem commonX2FrequencyMeasure_le_common (ν : ℝ≥0) :
    commonX2FrequencyMeasure ν ≤ commonFrequencyMeasure ν := by
  apply withDensity_mono
  exact Eventually.of_forall fun ξ => min_le_left _ _

theorem commonX2FrequencyMeasure_le_xm1 (ν : ℝ≥0) :
    commonX2FrequencyMeasure ν ≤ xm1FrequencyMeasure :=
  (commonX2FrequencyMeasure_le_common ν).trans (commonFrequencyMeasure_le_xm1 ν)

theorem commonX2FrequencyMeasure_le_viscousX1 (ν : ℝ≥0) :
    commonX2FrequencyMeasure ν ≤ viscousX1FrequencyMeasure ν :=
  (commonX2FrequencyMeasure_le_common ν).trans (commonFrequencyMeasure_le_viscousX1 ν)

/-- The degree-2 measure is absolutely continuous with respect to the
extended common carrier. -/
theorem x2FrequencyMeasure_absolutelyContinuous_commonX2
    (ν : ℝ≥0) (hν : 0 < ν) :
    x2FrequencyMeasure ≪ commonX2FrequencyMeasure ν :=
  (withDensity_absolutelyContinuous volume x2Density).trans
    (volume_absolutelyContinuous_commonX2FrequencyMeasure ν hν)

/-- The `X⁻¹` measure is absolutely continuous with respect to the extended
common carrier. -/
theorem xm1FrequencyMeasure_absolutelyContinuous_commonX2
    (ν : ℝ≥0) (hν : 0 < ν) :
    xm1FrequencyMeasure ≪ commonX2FrequencyMeasure ν :=
  (withDensity_absolutelyContinuous volume xm1Density).trans
    (volume_absolutelyContinuous_commonX2FrequencyMeasure ν hν)

/-- Restriction of an `X²` representative to the extended common carrier. -/
def x2SpatialToCommonX2 (ν : ℝ≥0) : X2Spatial →L[ℝ] CommonSpatialX2 ν :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonX2FrequencyMeasure_le_x2 ν)

/-- Restriction of an `X⁻¹` representative to the extended common carrier. -/
def xm1SpatialToCommonX2 (ν : ℝ≥0) : Xm1Spatial →L[ℝ] CommonSpatialX2 ν :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonX2FrequencyMeasure_le_xm1 ν)

theorem coeFn_x2SpatialToCommonX2 (ν : ℝ≥0) (f : X2Spatial) :
    x2SpatialToCommonX2 ν f =ᵐ[commonX2FrequencyMeasure ν] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonX2FrequencyMeasure_le_x2 ν) f

theorem coeFn_xm1SpatialToCommonX2 (ν : ℝ≥0) (f : Xm1Spatial) :
    xm1SpatialToCommonX2 ν f =ᵐ[commonX2FrequencyMeasure ν] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    (p := (1 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa using commonX2FrequencyMeasure_le_xm1 ν) f

theorem x2SpatialToCommonX2_injective (ν : ℝ≥0) (hν : 0 < ν) :
    Function.Injective (x2SpatialToCommonX2 ν) := by
  intro f g hfg
  apply Lp.ext
  apply (x2FrequencyMeasure_absolutelyContinuous_commonX2 ν hν).ae_eq
  filter_upwards [coeFn_x2SpatialToCommonX2 ν f, coeFn_x2SpatialToCommonX2 ν g]
    with ξ hfξ hgξ
  rw [← hfξ, ← hgξ, hfg]

theorem xm1SpatialToCommonX2_injective (ν : ℝ≥0) (hν : 0 < ν) :
    Function.Injective (xm1SpatialToCommonX2 ν) := by
  intro f g hfg
  apply Lp.ext
  apply (xm1FrequencyMeasure_absolutelyContinuous_commonX2 ν hν).ae_eq
  filter_upwards [coeFn_xm1SpatialToCommonX2 ν f, coeFn_xm1SpatialToCommonX2 ν g]
    with ξ hfξ hgξ
  rw [← hfξ, ← hgξ, hfg]

/-! ### Realization into the extended carrier (mirrors `realizeXm1Trajectory`) -/

/-- The `L∞_t X²` slot realized in the extended common trajectory carrier. -/
def realizeX2Trajectory (ν : ℝ≥0) (T : ℝ) :
    X2TimeSlot T →L[ℝ] CommonTrajectorySlotX2 ν T :=
  (lpTopToLpOne (E := CommonSpatialX2 ν) (leiLinTimeMeasure T)).comp
    ((x2SpatialToCommonX2 ν).compLpL ∞ (leiLinTimeMeasure T))

/-- The `L∞_t X⁻¹` slot realized in the extended common trajectory carrier. -/
def realizeXm1TrajectoryX2 (ν : ℝ≥0) (T : ℝ) :
    Xm1TimeSlot T →L[ℝ] CommonTrajectorySlotX2 ν T :=
  (lpTopToLpOne (E := CommonSpatialX2 ν) (leiLinTimeMeasure T)).comp
    ((xm1SpatialToCommonX2 ν).compLpL ∞ (leiLinTimeMeasure T))

theorem realizeX2Trajectory_injective (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) :
    Function.Injective (realizeX2Trajectory ν T) :=
  (lpTopToLpOne_injective (E := CommonSpatialX2 ν) (leiLinTimeMeasure T)).comp
    (compLpL_injective ∞ (leiLinTimeMeasure T) (x2SpatialToCommonX2 ν)
      (x2SpatialToCommonX2_injective ν hν))

/-! ## The extended box record -/

/-- **The Pattern-A carrier.**  An element of the actual linked box together
with a weight-degree-2 `L∞_t` slot which is realized, in the extended common
trajectory carrier, to the SAME spacetime trajectory as the `X⁻¹` slot, and
whose norm is bounded by `B3`. -/
abbrev ActualLinkedBoxX2 (ν : ℝ≥0) (T B1 B2 B3 : ℝ) :=
  { p : ↥(ActualLinkedBox ν T B1 B2) × X2TimeSlot T //
      ‖p.2‖ ≤ B3 ∧
        realizeX2Trajectory ν T p.2 =
          realizeXm1TrajectoryX2 ν T p.1.1.1.fst }

/-! ## Linkage extraction (mirrors `linked_spatial_representatives_ae` and
`raw_representatives_ae`) -/

theorem x2_linked_spatial_representatives_ae
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ) (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      xm1SpatialToCommonX2 ν ((b.1.1.1.1.fst : Xm1TimeSlot T) t) =
        x2SpatialToCommonX2 ν (b.1.2 t) := by
  let μ := leiLinTimeMeasure T
  let xm : Xm1TimeSlot T := b.1.1.1.1.fst
  let x2 : X2TimeSlot T := b.1.2
  let xmCommonTop := (xm1SpatialToCommonX2 ν).compLpL ∞ μ xm
  let x2CommonTop := (x2SpatialToCommonX2 ν).compLpL ∞ μ x2
  have hxmOuter : ∀ᵐ t ∂μ,
      ((lpTopToLpOne μ xmCommonTop : CommonTrajectorySlotX2 ν T) t) =
        (xmCommonTop t) := by
    filter_upwards with t
    rfl
  have hx2Outer : ∀ᵐ t ∂μ,
      ((lpTopToLpOne μ x2CommonTop : CommonTrajectorySlotX2 ν T) t) =
        (x2CommonTop t) := by
    filter_upwards with t
    rfl
  have hxmInner : ∀ᵐ t ∂μ,
      xmCommonTop t = xm1SpatialToCommonX2 ν (xm t) :=
    (xm1SpatialToCommonX2 ν).coeFn_compLpL xm
  have hx2Inner : ∀ᵐ t ∂μ,
      x2CommonTop t = x2SpatialToCommonX2 ν (x2 t) :=
    (x2SpatialToCommonX2 ν).coeFn_compLpL x2
  have hlinked : realizeX2Trajectory ν T x2 = realizeXm1TrajectoryX2 ν T xm :=
    b.2.2
  filter_upwards [hxmOuter, hx2Outer, hxmInner, hx2Inner] with t hxo hzo hxi hzi
  have hr' : (lpTopToLpOne μ x2CommonTop : ℝ → CommonSpatialX2 ν) t =
      (lpTopToLpOne μ xmCommonTop : ℝ → CommonSpatialX2 ν) t := by
    show (realizeX2Trajectory ν T x2 : ℝ → CommonSpatialX2 ν) t =
        (realizeXm1TrajectoryX2 ν T xm : ℝ → CommonSpatialX2 ν) t
    exact congrFun (congrArg (fun z : CommonTrajectorySlotX2 ν T =>
      (z : ℝ → CommonSpatialX2 ν)) hlinked) t
  rw [← hxi, ← hzi, hxo.symm, hzo.symm]
  exact hr'.symm

/-- At positive viscosity the extended linkage identifies the canonical
`X⁻¹` raw representative with the raw field of the `X²` slot for almost
every time. -/
theorem x2Raw_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      xm1RawRepresentative ν T b.1.1 t =ᵐ[volume]
        fun ξ : ES => ((b.1.2 t : X2Spatial) ξ : FourierCoordinateL1).ofLp := by
  filter_upwards [x2_linked_spatial_representatives_ae ν T B1 B2 B3 b] with t ht
  apply (volume_absolutelyContinuous_commonX2FrequencyMeasure ν hν).ae_eq
  have h1 : xm1SpatialToCommonX2 ν ((b.1.1.1.1.fst : Xm1TimeSlot T) t)
      =ᵐ[commonX2FrequencyMeasure ν] ((b.1.1.1.1.fst : Xm1TimeSlot T) t) :=
    coeFn_xm1SpatialToCommonX2 ν _
  have h2 : x2SpatialToCommonX2 ν (b.1.2 t)
      =ᵐ[commonX2FrequencyMeasure ν] (b.1.2 t : X2Spatial) :=
    coeFn_x2SpatialToCommonX2 ν _
  filter_upwards [h1, h2] with ξ h1 h2
  change (((b.1.1.1.1.fst : Xm1TimeSlot T) t : Xm1Spatial) ξ
    : FourierCoordinateL1).ofLp = _
  rw [← h1, ← h2, ht]

/-! ## The gated extended representative (mirrors `everywhereRawRepresentative`) -/

/-- Good time for the extended box: the original good-time conditions, the
almost-everywhere agreement of the canonical `X⁻¹` representative with the
raw field of the `X²` slot, and the pointwise `L∞` bound of the `X²` slot. -/
def BoxX2GoodAt (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (t : ℝ) : Prop :=
  RepresentativeGoodAt ν T b.1.1 t ∧
    (xm1RawRepresentative ν T b.1.1 t =ᵐ[volume]
      fun ξ : ES => ((b.1.2 t : X2Spatial) ξ : FourierCoordinateL1).ofLp) ∧
    ‖((b.1.2 : X2TimeSlot T) t)‖ ≤ ‖(b.1.2 : X2TimeSlot T)‖

/-- The canonical `L∞` slot section is bounded a.e. by the slot norm
(`X²` slot; mirrors `xm1TimeSlot_norm_ae`). -/
theorem x2TimeSlot_norm_ae
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ) (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      ‖((b.1.2 : X2TimeSlot T) t)‖ ≤ ‖(b.1.2 : X2TimeSlot T)‖ := by
  have h := ae_le_lpNorm_exponent_top (Lp.memLp (b.1.2 : X2TimeSlot T))
  have hnorm : lpNorm (fun t => (b.1.2 : X2TimeSlot T) t) ∞
      (leiLinTimeMeasure T) = ‖(b.1.2 : X2TimeSlot T)‖ := by
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable (b.1.2 : X2TimeSlot T)),
      ← Lp.norm_def]
  simpa only [hnorm] using h

/-- The good-time set of the extended box has full measure. -/
theorem boxX2GoodAt_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    ∀ᵐ t ∂leiLinTimeMeasure T, BoxX2GoodAt ν T B1 B2 B3 b t := by
  filter_upwards [representativeGoodAt_ae ν hν T b.1.1,
    x2Raw_ae ν hν T B1 B2 B3 b,
    x2TimeSlot_norm_ae ν T B1 B2 B3 b] with t h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- A single raw representative with the degree-2 moment at EVERY time: keep
the canonical representative at extended-good times, zero on the null
exceptional time set. -/
noncomputable def boxX2RawRepresentative (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) : ℝ → ES → ComplexSpace := by
  classical
  exact fun t => if BoxX2GoodAt ν T B1 B2 B3 b t then
    xm1RawRepresentative ν T b.1.1 t else 0

theorem boxX2RawRepresentative_at_good
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ) (b : ActualLinkedBoxX2 ν T B1 B2 B3)
    (t : ℝ) (ht : BoxX2GoodAt ν T B1 B2 B3 b t) :
    boxX2RawRepresentative ν T B1 B2 B3 b t =
      xm1RawRepresentative ν T b.1.1 t := by
  classical
  simp [boxX2RawRepresentative, ht]

theorem boxX2RawRepresentative_eq_everywhere_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      boxX2RawRepresentative ν T B1 B2 B3 b t =
        everywhereRawRepresentative ν T b.1.1 t := by
  filter_upwards [boxX2GoodAt_ae ν hν T B1 B2 B3 b,
    representativeGoodAt_ae ν hν T b.1.1] with t ht hg
  classical
  rw [boxX2RawRepresentative_at_good ν T B1 B2 B3 b t ht]
  symm
  simp [everywhereRawRepresentative, hg]

/-- The gated field has the `X⁻¹` coordinate integrability at every time. -/
theorem boxX2RawRepresentative_xm1_integrable
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖boxX2RawRepresentative ν T B1 B2 B3 b t ξ i‖) := by
  classical
  by_cases ht : BoxX2GoodAt ν T B1 B2 B3 b t
  · simpa [boxX2RawRepresentative_at_good ν T B1 B2 B3 b t ht] using
      xm1RawRepresentative_integrable ν T b.1.1 t i
  · simp [boxX2RawRepresentative, ht]

/-- The gated field has the `X¹` coordinate integrability at every time. -/
theorem boxX2RawRepresentative_x1_integrable
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ *
      ‖boxX2RawRepresentative ν T B1 B2 B3 b t ξ i‖) := by
  classical
  by_cases ht : BoxX2GoodAt ν T B1 B2 B3 b t
  · simpa [boxX2RawRepresentative_at_good ν T B1 B2 B3 b t ht] using ht.1.2.1 i
  · simp [boxX2RawRepresentative, ht]

/-- The gated field has the degree-2 coordinate integrability at every time:
at good times by transfer along the linkage a.e. equality, at exceptional
times because the field is zero. -/
theorem boxX2RawRepresentative_x2_integrable
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ 2 *
      ‖boxX2RawRepresentative ν T B1 B2 B3 b t ξ i‖) := by
  classical
  by_cases ht : BoxX2GoodAt ν T B1 B2 B3 b t
  · have h2 := x2Spatial_integrable_coordinate (b.1.2 t) i
    apply h2.congr
    filter_upwards [ht.2.1] with ξ hξ
    rw [boxX2RawRepresentative_at_good ν T B1 B2 B3 b t ht]
    rw [hξ]
  · simp [boxX2RawRepresentative, ht]

/-- The gated field is strongly measurable in frequency at every time. -/
theorem boxX2RawRepresentative_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable
      (fun ξ : ES => boxX2RawRepresentative ν T B1 B2 B3 b t ξ i) volume := by
  classical
  by_cases ht : BoxX2GoodAt ν T B1 B2 B3 b t
  · simpa [boxX2RawRepresentative_at_good ν T B1 B2 B3 b t ht] using
      xm1RawRepresentative_aestronglyMeasurable ν hν T b.1.1 t i
  · simpa [boxX2RawRepresentative, ht] using
      (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ES => (0 : ℂ)) volume)

/-! ## Part D — the extended record determines the budget legs -/

/-- Moment masses are insensitive to almost-everywhere changes of the raw
field. -/
theorem coordinateMomentMass_congr (k : ℕ) (u v : ES → ComplexSpace)
    (h : u =ᵐ[volume] v) :
    coordinateMomentMass k u = coordinateMomentMass k v := by
  unfold coordinateMomentMass
  refine Finset.sum_congr rfl (fun j _ => integral_congr_ae ?_)
  filter_upwards [h] with η hη
  rw [hη]

/-- **The degree split.**  The unweighted coordinate `X⁰` mass is dominated
by the homogeneous `X⁻¹` mass plus the degree-`2` moment mass: away from the
single frequency `ξ = 0`, `1 ≤ ‖ξ‖⁻¹ + ‖ξ‖²` splits as `‖ξ‖ ≤ 1` against the
`X⁻¹` weight and `1 ≤ ‖ξ‖` against the degree-`2` weight.  This is the exact
computation that makes the `X²` slot's own norm data determine the budget. -/
theorem coordinateX0Mass_le_xm1_add_moment2 (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hu1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hu2 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    coordinateX0Mass u ≤ coordinateXm1Mass u + coordinateMomentMass 2 u := by
  have hzero : ∀ᵐ η ∂(volume : Measure ES), (η : ES) ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hpnt (i : Fin 3) (η : ES) (hη : (η : ES) ≠ 0) :
      ‖u η i‖ ≤ ‖(η : ES)‖⁻¹ * ‖u η i‖ + ‖(η : ES)‖ ^ 2 * ‖u η i‖ := by
    have hpos : 0 < ‖(η : ES)‖ := norm_pos_iff.mpr hη
    have h1 : (1 : ℝ) ≤ ‖(η : ES)‖⁻¹ + ‖(η : ES)‖ ^ 2 := by
      rcases lt_or_ge ‖(η : ES)‖ 1 with hlt | hge
      · calc (1 : ℝ) ≤ ‖(η : ES)‖⁻¹ := (one_le_inv₀ hpos).mpr (le_of_lt hlt)
          _ ≤ ‖(η : ES)‖⁻¹ + ‖(η : ES)‖ ^ 2 :=
            le_add_of_nonneg_right (pow_nonneg (norm_nonneg η) 2)
      · have ht : ‖(η : ES)‖ ≤ ‖(η : ES)‖ ^ 2 := by
          calc ‖(η : ES)‖ = ‖(η : ES)‖ * 1 := (mul_one _).symm
            _ ≤ ‖(η : ES)‖ * ‖(η : ES)‖ :=
                mul_le_mul_of_nonneg_left hge (norm_nonneg η)
            _ = ‖(η : ES)‖ ^ 2 := (pow_two _).symm
        calc (1 : ℝ) ≤ ‖(η : ES)‖ := hge
          _ ≤ ‖(η : ES)‖ ^ 2 := ht
          _ ≤ ‖(η : ES)‖⁻¹ + ‖(η : ES)‖ ^ 2 :=
            le_add_of_nonneg_left (inv_nonneg.mpr (norm_nonneg η))
    calc ‖u η i‖ = (1 : ℝ) * ‖u η i‖ := (one_mul _).symm
      _ ≤ (‖(η : ES)‖⁻¹ + ‖(η : ES)‖ ^ 2) * ‖u η i‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖(η : ES)‖⁻¹ * ‖u η i‖ + ‖(η : ES)‖ ^ 2 * ‖u η i‖ := add_mul _ _ _
  unfold coordinateX0Mass coordinateXm1Mass coordinateMomentMass normXm1
  have hp (i : Fin 3) :
      ∫ ξ, ‖u ξ i‖ ≤ (∫ ξ, ‖ξ‖⁻¹ * ‖u ξ i‖) + ∫ ξ, ‖ξ‖ ^ 2 * ‖u ξ i‖ := by
    have hae : (fun ξ => ‖u ξ i‖) ≤ᵐ[volume]
        fun η => ‖(η : ES)‖⁻¹ * ‖u η i‖ + ‖(η : ES)‖ ^ 2 * ‖u η i‖ :=
      hzero.mono fun η hη => hpnt i η hη
    have hint : Integrable (fun ξ : ES => ‖u ξ i‖) :=
      ((hu1 i).add (hu2 i)).mono' (huM i).norm <|
        hzero.mono fun η hη => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          exact hpnt i η hη
    calc ∫ ξ, ‖u ξ i‖
        ≤ ∫ ξ, (‖ξ‖⁻¹ * ‖u ξ i‖ + ‖ξ‖ ^ 2 * ‖u ξ i‖) :=
            integral_mono_ae hint ((hu1 i).add (hu2 i)) hae
      _ = (∫ ξ, ‖ξ‖⁻¹ * ‖u ξ i‖) + ∫ ξ, ‖ξ‖ ^ 2 * ‖u ξ i‖ :=
            integral_add (hu1 i) (hu2 i)
  calc ∑ i : Fin 3, ∫ ξ, ‖u ξ i‖
      ≤ ∑ i : Fin 3, ((∫ ξ, ‖ξ‖⁻¹ * ‖u ξ i‖) + ∫ ξ, ‖ξ‖ ^ 2 * ‖u ξ i‖) :=
          Finset.sum_le_sum fun i _ => hp i
    _ = (∑ i : Fin 3, ∫ ξ, ‖ξ‖⁻¹ * ‖u ξ i‖) +
          ∑ i : Fin 3, ∫ ξ, ‖ξ‖ ^ 2 * ‖u ξ i‖ := Finset.sum_add_distrib

/-- Provider leg `hv0` for the gated extended representative: unweighted
coordinate integrability at every time. -/
theorem boxX2_hv0 (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (s : ℝ) (j : Fin 3) :
    Integrable (fun η : ES => ‖boxX2RawRepresentative ν T B1 B2 B3 b s η j‖) :=
  integrable_norm_coord_of_weighted_coords
    (boxX2RawRepresentative ν T B1 B2 B3 b s) j
    (boxX2RawRepresentative_aestronglyMeasurable ν hν T B1 B2 B3 b s j)
    (boxX2RawRepresentative_xm1_integrable ν T B1 B2 B3 b s j)
    (boxX2RawRepresentative_x1_integrable ν T B1 B2 B3 b s j)

/-- **The budget bound is now box data.**  The uniform `X⁰` mass bound
`coordinateMomentMass 0 (boxX2Raw s) ≤ B1 + B3` for every `s ∈ [0, T]`: the
degree split plus the `X⁻¹` box radius `B1` plus the `X²` slot radius `B3`.
This leg was undischarged for the degree-1 record (the `N02` barrier). -/
theorem boxX2_hbdd (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) (s : ℝ)
    (_hs : s ∈ Icc (0 : ℝ) T) :
    coordinateMomentMass 0 (boxX2RawRepresentative ν T B1 B2 B3 b s) ≤ B1 + B3 := by
  classical
  have hB1 : ‖b.1.1.1.1.fst‖ ≤ B1 := b.1.1.property.1
  rw [coordinateMomentMass_zero]
  by_cases ht : BoxX2GoodAt ν T B1 B2 B3 b s
  · refine le_trans
      (coordinateX0Mass_le_xm1_add_moment2
        (boxX2RawRepresentative ν T B1 B2 B3 b s)
        (fun i => boxX2RawRepresentative_aestronglyMeasurable ν hν T B1 B2 B3 b s i)
        (fun i => boxX2RawRepresentative_xm1_integrable ν T B1 B2 B3 b s i)
        (fun i => boxX2RawRepresentative_x2_integrable ν T B1 B2 B3 b s i))
      (add_le_add ?_ ?_)
    · have hew : boxX2RawRepresentative ν T B1 B2 B3 b s =
          everywhereRawRepresentative ν T b.1.1 s := by
        rw [boxX2RawRepresentative_at_good ν T B1 B2 B3 b s ht]
        simp [everywhereRawRepresentative, ht.1]
      rw [hew]
      exact Navier.Analysis.ContinuousLeiLinBoxRepresentative.coordinateXm1Mass_everywhere_le_of_mem_box ν hν T B1 B2 b.1.1 s
    · have hc : coordinateMomentMass 2 (boxX2RawRepresentative ν T B1 B2 B3 b s)
          = coordinateMomentMass 2
              (fun ξ : ES => ((b.1.2 s : X2Spatial) ξ : FourierCoordinateL1).ofLp) :=
        coordinateMomentMass_congr 2 _ _ <| by
          rw [boxX2RawRepresentative_at_good ν T B1 B2 B3 b s ht]
          exact ht.2.1
      rw [hc, ← norm_x2Spatial_eq]
      exact (ht.2.2).trans b.2.1
  · rw [boxX2RawRepresentative, if_neg ht]
    simp only [coordinateX0Mass, Pi.zero_apply, norm_zero, integral_zero,
      Finset.sum_const_zero]
    exact add_nonneg ((norm_nonneg (b.1.1.1.1.fst : Xm1TimeSlot T)).trans hB1)
      ((norm_nonneg (b.1.2 : X2TimeSlot T)).trans b.2.1)

/-- **The time-integrated degree-`2` moment is now box data**: the `X²` slot
is `L∞_t X²Spatial`, and on a finite time measure the inclusion
`L∞ ⊆ L¹` makes `s ↦ ‖(b.1.2) s‖` integrable; the gated representative's
degree-`2` mass agrees with it for almost every time. -/
theorem boxX2_hX2 (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3) :
    Integrable (fun s : ℝ =>
        coordinateMomentMass 2 (boxX2RawRepresentative ν T B1 B2 B3 b s))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  -- `L∞ → L¹` on the finite time measure, via the repo's own continuous
  -- inclusion `lpTopToLpOne` (probe-verified: its coe agrees pointwise with
  -- the slot, so `convert`/`ext`/`rfl` transports integrability).
  have h1 : Integrable (fun s : ℝ => (b.1.2 : X2TimeSlot T) s)
      (leiLinTimeMeasure T) := by
    have h := Lp.memLp (lpTopToLpOne (E := X2Spatial) (leiLinTimeMeasure T)
      (b.1.2 : X2TimeSlot T))
    have h1' : Integrable (fun s : ℝ => (lpTopToLpOne (E := X2Spatial)
        (leiLinTimeMeasure T) (b.1.2 : X2TimeSlot T)) s) (leiLinTimeMeasure T) :=
      memLp_one_iff_integrable.mp h
    convert h1' using 1
    ext s
    rfl
  have h2 : Integrable (fun s : ℝ => ‖(b.1.2 : X2TimeSlot T) s‖)
      (leiLinTimeMeasure T) := h1.norm
  have hcae : (fun s : ℝ =>
      coordinateMomentMass 2 (boxX2RawRepresentative ν T B1 B2 B3 b s))
      =ᵐ[leiLinTimeMeasure T]
      (fun s : ℝ => ‖((b.1.2 : X2TimeSlot T) s : X2Spatial)‖) := by
    filter_upwards [boxX2GoodAt_ae ν hν T B1 B2 B3 b] with s hs
    rw [coordinateMomentMass_congr 2
        (boxX2RawRepresentative ν T B1 B2 B3 b s)
        (fun ξ : ES => ((b.1.2 s : X2Spatial) ξ : FourierCoordinateL1).ofLp) <| by
          rw [boxX2RawRepresentative_at_good ν T B1 B2 B3 b s hs]
          exact hs.2.1]
    rw [← norm_x2Spatial_eq]
  exact h2.congr hcae.symm

/-- **The extended record supplies the `X⁰·X²` budget** once the single
remaining leg — joint continuity of the gated representative — is granted.
Three of the four budget legs (`hbdd`, `hv2`, `hX2`) are now theses about the
box, not hypotheses. -/
theorem boxX2_sourceX2Budget_of_hv (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3)
    (hv : ∀ j : Fin 3,
      Continuous (fun p : ES × ℝ =>
        boxX2RawRepresentative ν T B1 B2 B3 b p.2 p.1 j)) :
    SourceX2Budget T (boxX2RawRepresentative ν T B1 B2 B3 b) :=
  ⟨B1 + B3, hv, boxX2_hbdd ν hν T B1 B2 B3 b,
    boxX2RawRepresentative_x2_integrable ν T B1 B2 B3 b,
    boxX2_hX2 ν hν T B1 B2 B3 b⟩

/-- **The extended record plus joint continuity gives `SourceL1X1`** through
the existing moment-bound provider.  Compare
`sourceL1X1_of_box_sourceX2Budget`, which needed the full `SourceX2Budget` as
a hypothesis; here the record itself constructs the budget from its `X²` slot. -/
theorem boxX2_sourceL1X1_of_hv (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2 ν T B1 B2 B3)
    (hv : ∀ j : Fin 3,
      Continuous (fun p : ES × ℝ =>
        boxX2RawRepresentative ν T B1 B2 B3 b p.2 p.1 j)) :
    SourceL1X1 T (boxX2RawRepresentative ν T B1 B2 B3 b) := by
  obtain ⟨U0, hv', hbdd, hv2, hX2⟩ :=
    boxX2_sourceX2Budget_of_hv ν hν T B1 B2 B3 b hv
  exact Navier.Analysis.ContinuousLeiLinSourceX1MomentBound.sourceL1X1_of_continuous_uniformX0_integrableX2 T
    (boxX2RawRepresentative ν T B1 B2 B3 b) U0 hv'
    (boxX2_hv0 ν hν T B1 B2 B3 b) hv2 hbdd hX2

/-! ## Slot construction and suppliers -/

/-- The exact spatial `X²` representative of a raw time-frequency field
(mirrors `xm1Section`). -/
def x2Section (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huX2 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u t ξ i‖)) (t : ℝ) :
    X2Spatial :=
  toX2Spatial (u t) (huM t) (huX2 t)

theorem norm_x2Section (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huX2 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u t ξ i‖)) (t : ℝ) :
    ‖x2Section u huM huX2 t‖ = coordinateMomentMass 2 (u t) :=
  norm_toX2Spatial (u t) (huM t) (huX2 t)

/-- A uniform `X²` budget and strong measurability in the new spatial
quotient construct the finite-horizon essential-supremum slot (mirrors
`toXm1TimeSlot`). -/
def toX2TimeSlot (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huX2 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u t ξ i‖))
    (T B : ℝ)
    (hTimeM : AEStronglyMeasurable (x2Section u huM huX2)
      (leiLinTimeMeasure T))
    (hB : ∀ t ∈ Icc (0 : ℝ) T, coordinateMomentMass 2 (u t) ≤ B) :
    X2TimeSlot T :=
  (memLp_top_of_bound hTimeM B <| by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    simpa [norm_x2Section] using hB t ht).toLp (x2Section u huM huX2)

theorem coeFn_toX2TimeSlot (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huX2 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u t ξ i‖))
    (T B : ℝ)
    (hTimeM : AEStronglyMeasurable (x2Section u huM huX2)
      (leiLinTimeMeasure T))
    (hB : ∀ t ∈ Icc (0 : ℝ) T, coordinateMomentMass 2 (u t) ≤ B) :
    toX2TimeSlot u huM huX2 T B hTimeM hB =ᵐ[leiLinTimeMeasure T]
      x2Section u huM huX2 :=
  MemLp.coeFn_toLp _

/-- The `X⁻¹` and `X²` spatial representatives built from the same raw
Fourier field agree in the extended common positive-density quotient
(mirrors `spatial_realizations_eq`). -/
theorem spatial_x2_realizations_eq (ν : ℝ≥0) (u : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (huXm1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (huX2 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u ξ i‖)) :
    xm1SpatialToCommonX2 ν (toXm1Spatial u huM huXm1) =
      x2SpatialToCommonX2 ν (toX2Spatial u huM huX2) := by
  apply Lp.ext
  have hcXm1 : commonX2FrequencyMeasure ν ≪ xm1FrequencyMeasure :=
    Measure.absolutelyContinuous_of_le (commonX2FrequencyMeasure_le_xm1 ν)
  have hcX2 : commonX2FrequencyMeasure ν ≪ x2FrequencyMeasure :=
    Measure.absolutelyContinuous_of_le (commonX2FrequencyMeasure_le_x2 ν)
  have hxmRep : toXm1Spatial u huM huXm1 =ᵐ[commonX2FrequencyMeasure ν]
      coordinateL1 u :=
    hcXm1.ae_eq (coeFn_toXm1Spatial u huM huXm1)
  have hx2Rep : toX2Spatial u huM huX2 =ᵐ[commonX2FrequencyMeasure ν]
      coordinateL1 u :=
    hcX2.ae_eq (coeFn_toX2Spatial u huM huX2)
  filter_upwards [coeFn_xm1SpatialToCommonX2 ν (toXm1Spatial u huM huXm1),
    coeFn_x2SpatialToCommonX2 ν (toX2Spatial u huM huX2), hxmRep, hx2Rep]
    with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- The `X⁻¹` slot and the new `X²` slot, both constructed from one raw
spacetime field, realize to the same extended common trajectory (mirrors
`realized_time_slots_eq_of_raw`). -/
theorem realized_x2_time_slots_eq_of_raw
    (ν : ℝ≥0) (T R B : ℝ) (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (huX2 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖u t ξ i‖))
    (hXm1TimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hXm1Bound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ R)
    (hx2TimeM : AEStronglyMeasurable (x2Section u huM huX2)
      (leiLinTimeMeasure T))
    (hxBound : ∀ t ∈ Icc (0 : ℝ) T, coordinateMomentMass 2 (u t) ≤ B) :
    realizeX2Trajectory ν T
        (toX2TimeSlot u huM huX2 T B hx2TimeM hxBound) =
      realizeXm1TrajectoryX2 ν T
        (toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound) := by
  let μ := leiLinTimeMeasure T
  let xm := toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound
  let x2 := toX2TimeSlot u huM huX2 T B hx2TimeM hxBound
  let xmCommonTop := (xm1SpatialToCommonX2 ν).compLpL ∞ μ xm
  let x2CommonTop := (x2SpatialToCommonX2 ν).compLpL ∞ μ x2
  have hxmOuter : ∀ᵐ t ∂μ,
      ((lpTopToLpOne μ xmCommonTop : ℝ → CommonSpatialX2 ν) t) =
        (xmCommonTop t) := by
    filter_upwards with t
    rfl
  have hx2Outer : ∀ᵐ t ∂μ,
      ((lpTopToLpOne μ x2CommonTop : ℝ → CommonSpatialX2 ν) t) =
        (x2CommonTop t) := by
    filter_upwards with t
    rfl
  have hxmInner : ∀ᵐ t ∂μ,
      xmCommonTop t = xm1SpatialToCommonX2 ν (xm t) :=
    (xm1SpatialToCommonX2 ν).coeFn_compLpL xm
  have hx2Inner : ∀ᵐ t ∂μ,
      x2CommonTop t = x2SpatialToCommonX2 ν (x2 t) :=
    (x2SpatialToCommonX2 ν).coeFn_compLpL x2
  have hxmRep : Filter.EventuallyEq (ae μ)
      (fun t => (((xm : Xm1TimeSlot T) : ℝ → Xm1Spatial) t))
      (xm1Section u huM huXm1) := by
    simpa [μ, xm] using
      coeFn_toXm1TimeSlot u huM huXm1 T R hXm1TimeM hXm1Bound
  have hx2Rep : Filter.EventuallyEq (ae μ)
      (fun t => (((x2 : X2TimeSlot T) : ℝ → X2Spatial) t))
      (x2Section u huM huX2) := by
    simpa [μ, x2] using
      coeFn_toX2TimeSlot u huM huX2 T B hx2TimeM hxBound
  apply Lp.ext
  filter_upwards [hxmOuter, hx2Outer, hxmInner, hx2Inner, hxmRep, hx2Rep] with
    t hxo hzo hxi hzi hxr hzr
  rw [show realizeXm1TrajectoryX2 ν T xm = lpTopToLpOne μ xmCommonTop by rfl,
    show realizeX2Trajectory ν T x2 = lpTopToLpOne μ x2CommonTop by rfl]
  rw [hxo, hzo, hxi, hzi, hxr, hzr]
  exact (spatial_x2_realizations_eq ν (u t) (huM t) (huXm1 t) (huX2 t)).symm

/-- **Non-vacuity of the extended record (zero supplier).** The zero linked
carrier element together with the zero `X²` slot inhabits the extended box at
radii `0`, so the extended box is never empty. -/
noncomputable def boxX2Zero (ν : ℝ≥0) (T : ℝ) :
    ActualLinkedBoxX2 ν T 0 0 0 :=
  ⟨⟨⟨linkedAdmissibleZero (realizeXm1Trajectory ν T)
        (realizeViscousX1Trajectory ν T),
      by
        constructor
        · simpa [linkedAdmissibleZero] using (le_refl (0 : ℝ))
        · simpa [linkedAdmissibleZero] using (le_refl (0 : ℝ))⟩,
      (0 : X2TimeSlot T)⟩,
    ⟨norm_zero.le, by simp [linkedAdmissibleZero, map_zero]⟩⟩

/-! ### The nonzero supplier: the constant Fourier datum -/

/-- The `X⁻¹` slot of the time-constant Fourier datum. -/
noncomputable def constRawXm (T : ℝ) (u₀ : SchwartzVelocity) :
    Xm1TimeSlot T :=
  toXm1TimeSlot (fun _ => fourierDatum u₀)
    (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
    (fun t i => fourierDatum_integrable_Xm1 u₀ i) T
    (coordinateXm1Mass (fourierDatum u₀))
    (by
      have hsec :
          (xm1Section (fun _ => fourierDatum u₀)
            (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
            (fun t i => fourierDatum_integrable_Xm1 u₀ i)) =
          (fun _ : ℝ => toXm1Spatial (fourierDatum u₀)
            (fun i => fourierDatum_aestronglyMeasurable u₀ i)
            (fun i => fourierDatum_integrable_Xm1 u₀ i)) := by
        funext t
        rfl
      rw [hsec]
      exact aestronglyMeasurable_const)
    (fun t _ => le_refl _)

/-- The viscous `X¹` slot of the time-constant Fourier datum. -/
noncomputable def constRawX1 (ν : ℝ≥0) (T : ℝ) (u₀ : SchwartzVelocity) :
    ViscousX1TimeSlot ν T :=
  toViscousX1TimeSlot (fun _ => fourierDatum u₀)
    (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
    (fun t i => fourierDatum_integrable_X1 u₀ i) ν T
    (by
      have hsec :
          (viscousX1Section (fun _ => fourierDatum u₀)
            (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
            (fun t i => fourierDatum_integrable_X1 u₀ i) ν) =
          (fun _ : ℝ => toViscousX1Spatial ν (fourierDatum u₀)
            (fun i => fourierDatum_aestronglyMeasurable u₀ i)
            (fun i => fourierDatum_integrable_X1 u₀ i)) := by
        funext t
        rfl
      rw [hsec]
      exact aestronglyMeasurable_const)
    (by
      show Integrable (fun _ : ℝ => coordinateX1Mass (fourierDatum u₀))
        (leiLinTimeMeasure T)
      exact integrableOn_const measure_Icc_lt_top.ne)

/-- Every time coordinate of the time-constant Fourier datum has the
degree-`2` weighted integrability (the Schwartz integrability API). -/
theorem constRawX2_coordInt (u₀ : SchwartzVelocity) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES =>
      ‖ξ‖ ^ 2 * ‖(fun _ => fourierDatum u₀) t ξ i‖) := by
  simpa [fourierDatum] using
    (𝓕 (euclidComponent u₀ i) : SchwartzMap ES ℂ).integrable_pow_mul volume 2

/-- The new `X²` slot of the time-constant Fourier datum: the slot the degree-1
record could not carry. -/
noncomputable def constRawX2 (T : ℝ) (u₀ : SchwartzVelocity) : X2TimeSlot T :=
  toX2TimeSlot (fun _ => fourierDatum u₀)
    (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
    (constRawX2_coordInt u₀) T
    (coordinateMomentMass 2 (fourierDatum u₀))
    (by
      have hsec :
          (x2Section (fun _ => fourierDatum u₀)
            (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
            (constRawX2_coordInt u₀)) =
          (fun _ : ℝ => toX2Spatial (fourierDatum u₀)
            (fun i => fourierDatum_aestronglyMeasurable u₀ i)
            (constRawX2_coordInt u₀ 0)) := by
        funext t
        rfl
      rw [hsec]
      exact aestronglyMeasurable_const)
    (fun t _ => le_refl _)

/-- **Non-vacuity with a constructed nonzero slot.**  For the time-constant
raw field `fourierDatum u₀`, the constructed `X⁻¹`/`X¹` linked carrier element
and the constructed `X²` slot satisfy the extended linkage; taking the three
constructed slot norms as radii gives a constructed element of the extended
box at every positive viscosity.  The `X²` radius `B3` is genuinely new
record data: for this element it is `‖constRawX2 T u₀‖ =` the degree-`2`
moment mass, a finite number the degree-1 record could not carry. -/
noncomputable def boxX2Constant (ν : ℝ≥0) (T : ℝ) (u₀ : SchwartzVelocity) :
    ActualLinkedBoxX2 ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
      ‖constRawX2 T u₀‖ :=
  ⟨⟨⟨actualLinkedOfRaw ν T (coordinateXm1Mass (fourierDatum u₀))
      (fun _ => fourierDatum u₀)
      (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
      (fun t i => fourierDatum_integrable_Xm1 u₀ i)
      (fun t i => fourierDatum_integrable_X1 u₀ i)
      (by
        have hsec :
            (xm1Section (fun _ => fourierDatum u₀)
              (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
              (fun t i => fourierDatum_integrable_Xm1 u₀ i)) =
            (fun _ : ℝ => toXm1Spatial (fourierDatum u₀)
              (fun i => fourierDatum_aestronglyMeasurable u₀ i)
              (fun i => fourierDatum_integrable_Xm1 u₀ i)) := by
          funext t
          rfl
        rw [hsec]
        exact aestronglyMeasurable_const)
      (by
        have hsec :
            (viscousX1Section (fun _ => fourierDatum u₀)
              (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
              (fun t i => fourierDatum_integrable_X1 u₀ i) ν) =
            (fun _ : ℝ => toViscousX1Spatial ν (fourierDatum u₀)
              (fun i => fourierDatum_aestronglyMeasurable u₀ i)
              (fun i => fourierDatum_integrable_X1 u₀ i)) := by
          funext t
          rfl
        rw [hsec]
        exact aestronglyMeasurable_const)
      (fun t _ => le_refl _)
      (by
        show Integrable (fun _ : ℝ => coordinateX1Mass (fourierDatum u₀))
          (leiLinTimeMeasure T)
        exact integrableOn_const measure_Icc_lt_top.ne),
    ⟨le_refl _, le_refl _⟩⟩,
    constRawX2 T u₀⟩,
    ⟨le_refl _,
      realized_x2_time_slots_eq_of_raw ν T
        (coordinateXm1Mass (fourierDatum u₀))
        (coordinateMomentMass 2 (fourierDatum u₀)) (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun t i => fourierDatum_integrable_Xm1 u₀ i)
        (constRawX2_coordInt u₀)
        (by
          have hsec :
              (xm1Section (fun _ => fourierDatum u₀)
                (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun t i => fourierDatum_integrable_Xm1 u₀ i)) =
              (fun _ : ℝ => toXm1Spatial (fourierDatum u₀)
                (fun i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun i => fourierDatum_integrable_Xm1 u₀ i)) := by
            funext t
            rfl
          rw [hsec]
          exact aestronglyMeasurable_const)
        (fun t _ => le_refl _)
        (by
          have hsec :
              (x2Section (fun _ => fourierDatum u₀)
                (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
                (constRawX2_coordInt u₀)) =
              (fun _ : ℝ => toX2Spatial (fourierDatum u₀)
                (fun i => fourierDatum_aestronglyMeasurable u₀ i)
                (constRawX2_coordInt u₀ 0)) := by
            funext t
            rfl
          rw [hsec]
          exact aestronglyMeasurable_const)
        (fun t _ => le_refl _)⟩⟩

end Navier.Analysis.LinkedBoxX2Carrier

set_option pp.fullNames true in
#check @Navier.Analysis.LinkedBoxX2Carrier.coordinateMomentMass_congr
#check @Navier.Analysis.LinkedBoxX2Carrier.coordinateX0Mass_le_xm1_add_moment2
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2_hv0
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2_hbdd
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2_hX2
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceX2Budget_of_hv
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv
#check @Navier.Analysis.LinkedBoxX2Carrier.x2Section
#check @Navier.Analysis.LinkedBoxX2Carrier.toX2TimeSlot
#check @Navier.Analysis.LinkedBoxX2Carrier.spatial_x2_realizations_eq
#check @Navier.Analysis.LinkedBoxX2Carrier.realized_x2_time_slots_eq_of_raw
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2Zero
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2Constant
#check @Navier.Analysis.LinkedBoxX2Carrier.x2_linked_spatial_representatives_ae
#check @Navier.Analysis.LinkedBoxX2Carrier.x2Raw_ae
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2GoodAt_ae
#check @Navier.Analysis.LinkedBoxX2Carrier.boxX2RawRepresentative_eq_everywhere_ae

#print axioms Navier.Analysis.LinkedBoxX2Carrier.coordinateMomentMass_congr
#print axioms Navier.Analysis.LinkedBoxX2Carrier.coordinateX0Mass_le_xm1_add_moment2
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_hv0
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_hbdd
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_hX2
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceX2Budget_of_hv
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv
#print axioms Navier.Analysis.LinkedBoxX2Carrier.spatial_x2_realizations_eq
#print axioms Navier.Analysis.LinkedBoxX2Carrier.realized_x2_time_slots_eq_of_raw
#print axioms Navier.Analysis.LinkedBoxX2Carrier.x2_linked_spatial_representatives_ae
#print axioms Navier.Analysis.LinkedBoxX2Carrier.x2Raw_ae
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2GoodAt_ae
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2RawRepresentative_eq_everywhere_ae
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2RawRepresentative_x2_integrable
