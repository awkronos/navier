import Navier.Analysis.ContinuousLeiLinTrajectoryLift

/-!
# Representative invariance of the continuous Lei--Lin mild map

The complete trajectory carrier is a pair of Bochner `Lᵖ` quotients.  Hence a
map on that carrier must not depend on the chosen spacetime representatives.
This file proves the analytic descent fact for the literal whole-space mild
operator.  Frequencywise convolution respects almost-everywhere equality by
translation invariance of Lebesgue measure; the Duhamel integral then respects
almost-everywhere equality in time on every smaller causal interval.

The final theorem connects this directly to equality in the actual `X⁻¹`
time slot.  It does not select a continuous representative and does not add a
trajectory-existence hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Convolution
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift

namespace Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

/-- The literal continuous Navier bilinear symbol is invariant under changes
of either input on a Lebesgue-null set.  The conclusion is equality at every
output frequency because convolution itself is defined by an integral. -/
theorem continuousNavierBilinear_congr_ae
    (u u' v v' : ES → ComplexSpace)
    (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v') :
    continuousNavierBilinear u v = continuousNavierBilinear u' v' := by
  have hconv (i j : Fin 3) :
      ((fun η : ES => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => v η i)) =
        ((fun η : ES => u' η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => v' η i)) := by
    apply convolution_congr
    · filter_upwards [hu] with η hη
      rw [hη]
    · filter_upwards [hv] with η hη
      rw [hη]
  have hraw : rawNavierConvection u v = rawNavierConvection u' v' := by
    funext ξ i
    unfold rawNavierConvection
    apply Finset.sum_congr rfl
    intro j hj
    rw [hconv i j]
  funext ξ
  unfold continuousNavierBilinear
  rw [hraw]

/-- Nested spacetime a.e. equality makes the continuous Navier source equal
for almost every time, at every output frequency. -/
theorem continuousNavierSource_congr_ae
    (T : ℝ) (u v : ℝ → ES → ComplexSpace)
    (huv : ∀ᵐ s ∂leiLinTimeMeasure T, u s =ᵐ[volume] v s) :
    ∀ᵐ s ∂leiLinTimeMeasure T,
      continuousNavierSource u u s = continuousNavierSource v v s := by
  filter_upwards [huv] with s hs
  exact continuousNavierBilinear_congr_ae (u s) (v s) (u s) (v s) hs hs

/-- If two trajectories agree a.e. on the finite horizon, their causal
Duhamel terms agree at every frequency and every time in that horizon. -/
theorem continuousDuhamel_congr_ae_on_horizon
    (ν T : ℝ) (u v : ℝ → ES → ComplexSpace)
    (huv : ∀ᵐ s ∂leiLinTimeMeasure T, u s =ᵐ[volume] v s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (ξ : ES) :
    continuousDuhamel ν u u t ξ = continuousDuhamel ν v v t ξ := by
  have hsource := continuousNavierSource_congr_ae T u v huv
  change ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      continuousNavierSource u u s = continuousNavierSource v v s at hsource
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hsource_t : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      continuousNavierSource u u s = continuousNavierSource v v s :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hsource
  funext i
  apply integral_congr_ae
  filter_upwards [hsource_t] with s hs
  rw [hs]

/-- The whole-space mild operator therefore descends through nested spacetime
a.e. equality on its causal horizon. -/
theorem continuousMildImage_congr_ae_on_horizon
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (a : ES → ComplexSpace)
    (u v : ℝ → ES → ComplexSpace)
    (huv : ∀ᵐ s ∂leiLinTimeMeasure T, u s =ᵐ[volume] v s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (ξ : ES) :
    continuousMildImage ν hν a u t ξ =
      continuousMildImage ν hν a v t ξ := by
  unfold continuousMildImage
  rw [continuousDuhamel_congr_ae_on_horizon ν T u v huv t ht ξ]

/-- Equality of two concrete `X⁻¹` time-slot presentations forces equality of
their raw spacetime fields almost everywhere for time and Lebesgue frequency.
This is the exact quotient bridge used by the descent theorem below. -/
theorem nested_ae_eq_of_toXm1TimeSlot_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T Ru Rv : ℝ)
    (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (hvM : ∀ t i, AEStronglyMeasurable (fun ξ => v t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (hvXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v t ξ i‖))
    (huTimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hvTimeM : AEStronglyMeasurable (xm1Section v hvM hvXm1)
      (leiLinTimeMeasure T))
    (huBound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ Ru)
    (hvBound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (v t) ≤ Rv)
    (hslot : toXm1TimeSlot u huM huXm1 T Ru huTimeM huBound =
      toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvBound) :
    ∀ᵐ t ∂leiLinTimeMeasure T, u t =ᵐ[volume] v t := by
  have hvolXm1 : volume ≪ xm1FrequencyMeasure :=
    (volume_absolutelyContinuous_commonFrequencyMeasure ν hν).trans
      (Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_xm1 ν))
  have huRep := coeFn_toXm1TimeSlot u huM huXm1 T Ru huTimeM huBound
  have hvRep := coeFn_toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvBound
  filter_upwards [huRep, hvRep] with t hut hvt
  have hsections : xm1Section u huM huXm1 t = xm1Section v hvM hvXm1 t := by
    rw [← hut, ← hvt, hslot]
  have huSpatial := coeFn_toXm1Spatial (u t) (huM t) (huXm1 t)
  have hvSpatial := coeFn_toXm1Spatial (v t) (hvM t) (hvXm1 t)
  apply hvolXm1.ae_eq
  filter_upwards [huSpatial, hvSpatial] with ξ huξ hvξ
  have heval :
      ((xm1Section u huM huXm1 t : Xm1Spatial) : ES → FourierCoordinateL1) ξ =
        ((xm1Section v hvM hvXm1 t : Xm1Spatial) : ES → FourierCoordinateL1) ξ :=
    congrArg (fun z : Xm1Spatial => z ξ) hsections
  have hcoord : coordinateL1 (u t) ξ = coordinateL1 (v t) ξ := by
    exact huξ.symm.trans (heval.trans hvξ)
  simpa [coordinateL1] using
    congrArg (fun z : FourierCoordinateL1 => z.ofLp) hcoord

/-- Original quotient consumer: equality of the actual `X⁻¹` slot inputs is
enough to make the literal continuous mild images equal throughout the causal
horizon.  Thus the operator does not depend on raw representatives. -/
theorem continuousMildImage_congr_of_toXm1TimeSlot_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T Ru Rv : ℝ)
    (a : ES → ComplexSpace) (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (hvM : ∀ t i, AEStronglyMeasurable (fun ξ => v t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (hvXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v t ξ i‖))
    (huTimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hvTimeM : AEStronglyMeasurable (xm1Section v hvM hvXm1)
      (leiLinTimeMeasure T))
    (huBound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ Ru)
    (hvBound : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (v t) ≤ Rv)
    (hslot : toXm1TimeSlot u huM huXm1 T Ru huTimeM huBound =
      toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvBound)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (ξ : ES) :
    continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a u t ξ =
      continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a v t ξ := by
  exact continuousMildImage_congr_ae_on_horizon (ν : ℝ) (by exact_mod_cast hν)
    T a u v
    (nested_ae_eq_of_toXm1TimeSlot_eq ν hν T Ru Rv u v
      huM hvM huXm1 hvXm1 huTimeM hvTimeM huBound hvBound hslot)
    t ht ξ

end Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousNavierBilinear_congr_ae
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousDuhamel_congr_ae_on_horizon
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousMildImage_congr_ae_on_horizon
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.nested_ae_eq_of_toXm1TimeSlot_eq
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeInvariant.continuousMildImage_congr_of_toXm1TimeSlot_eq
