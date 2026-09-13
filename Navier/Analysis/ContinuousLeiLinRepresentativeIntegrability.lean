import Navier.Analysis.ContinuousLeiLinCommonRepresentative
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Weighted integrability of canonical linked-carrier representatives

The two canonical raw representatives extracted from the actual linked
trajectory carry their defining spatial integrability directly from the `L¹`
quotients. Since linkage identifies them almost everywhere, the `X⁻¹`
representative also has `X¹` integrability for almost every horizon time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative

namespace Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability

/-- Every element of the exact spatial `X⁻¹` quotient has an integrable raw
coordinate with the literal homogeneous weight. -/
theorem xm1Spatial_integrable_coordinate (f : Xm1Spatial) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(f ξ : FourierCoordinateL1).ofLp i‖) := by
  have hf : Integrable (fun ξ : ES => (f ξ : FourierCoordinateL1))
      xm1FrequencyMeasure :=
    memLp_one_iff_integrable.mp (Lp.memLp f)
  have hsmul : Integrable (fun ξ : ES =>
      (xm1Density ξ).toReal • (f ξ : FourierCoordinateL1)) volume := by
    exact (integrable_withDensity_iff_integrable_smul'
      (ENNReal.measurable_ofReal.comp measurable_norm.inv)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hf
  have hi : Integrable (fun ξ : ES =>
      ((xm1Density ξ).toReal • (f ξ : FourierCoordinateL1)) i) volume :=
    hsmul.eval_piLp i
  apply hi.norm.congr
  filter_upwards [xm1Density_toReal_ae] with ξ hξ
  change ‖(xm1Density ξ).toReal • (f ξ : FourierCoordinateL1).ofLp i‖ = _
  rw [norm_smul, hξ]
  simp

/-- Every element of the viscosity-weighted `X¹` quotient has the literal
unscaled `X¹` coordinate integrability when viscosity is positive. -/
theorem viscousX1Spatial_integrable_coordinate
    (ν : ℝ≥0) (hν : 0 < ν) (f : ViscousX1Spatial ν) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖(f ξ : FourierCoordinateL1).ofLp i‖) := by
  have hf : Integrable (fun ξ : ES => (f ξ : FourierCoordinateL1))
      (viscousX1FrequencyMeasure ν) :=
    memLp_one_iff_integrable.mp (Lp.memLp f)
  have hsmul : Integrable (fun ξ : ES =>
      (viscousX1Density ν ξ).toReal • (f ξ : FourierCoordinateL1)) volume := by
    exact (integrable_withDensity_iff_integrable_smul'
      (measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_norm))
      (Eventually.of_forall fun _ =>
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)).mp hf
  have hi : Integrable (fun ξ : ES =>
      ((viscousX1Density ν ξ).toReal • (f ξ : FourierCoordinateL1)) i) volume :=
    hsmul.eval_piLp i
  have hscaled : Integrable (fun ξ : ES =>
      (ν : ℝ) * (‖ξ‖ * ‖(f ξ : FourierCoordinateL1).ofLp i‖)) volume := by
    apply hi.norm.congr
    filter_upwards with ξ
    change ‖(viscousX1Density ν ξ).toReal •
      (f ξ : FourierCoordinateL1).ofLp i‖ = _
    rw [norm_smul, viscousX1Density_toReal]
    rw [Real.norm_of_nonneg (mul_nonneg NNReal.zero_le_coe (norm_nonneg ξ))]
    ring
  have hunscaled := hscaled.const_mul ((ν : ℝ)⁻¹)
  apply hunscaled.congr
  filter_upwards with ξ
  field_simp

/-- The canonical `X⁻¹` raw representative has its defining spatial
integrability at every time. -/
theorem xm1RawRepresentative_integrable
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖xm1RawRepresentative ν T x t ξ i‖) := by
  exact xm1Spatial_integrable_coordinate ((x.1.fst : Xm1TimeSlot T) t) i

/-- The canonical viscous `X¹` raw representative has its defining spatial
integrability at every time. -/
theorem viscousX1RawRepresentative_integrable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ *
      ‖viscousX1RawRepresentative ν T x t ξ i‖) := by
  exact viscousX1Spatial_integrable_coordinate ν hν
    ((x.1.snd : ViscousX1TimeSlot ν T) t) i

/-- Linkage transfers `X¹` integrability to the canonical `X⁻¹` raw
representative for almost every time on the finite horizon. -/
theorem xm1RawRepresentative_x1_integrable_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T, ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖xm1RawRepresentative ν T x t ξ i‖) := by
  filter_upwards [raw_representatives_ae ν hν T x] with t ht
  intro i
  apply (viscousX1RawRepresentative_integrable ν hν T x t i).congr
  filter_upwards [ht] with ξ hξ
  rw [hξ]

end Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability

#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability.xm1Spatial_integrable_coordinate
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability.viscousX1Spatial_integrable_coordinate
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability.xm1RawRepresentative_integrable
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability.viscousX1RawRepresentative_integrable
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability.xm1RawRepresentative_x1_integrable_ae
