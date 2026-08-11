import Navier.Analysis.ContinuousLeiLinSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Time-Duhamel carrier for the continuous Lei--Lin symbol

This is the literal time-dependent continuous Fourier carrier.  Its bilinear
source is the vector symbol from `ContinuousLeiLinSpace`; the Duhamel operator
then applies the output heat multiplier and integrates over the past interval.

The proved estimate is deliberately stated at the level justified by the
available continuous analysis: the `L¹_t X⁻¹` mass of the source is bounded by
the time integral of the product of the two coordinate `X⁰` masses.  This is
the exact vector-coordinate form of the fixed-time convolution estimate.  A
further `X⁻¹/X¹` mixed estimate needs a continuous weighted interpolation and
Bochner/Fubini bridge, neither of which is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.ContinuousLeiLinTimeDuhamel

open MeasureTheory Set
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm

/-- The literal continuous Fourier Navier source at time `t`. -/
def continuousNavierSource (u v : ℝ → ES → ComplexSpace) (t : ℝ) :
    ES → ComplexSpace :=
  continuousNavierBilinear (u t) (v t)

/-- The coordinate `X⁰` mass of a vector Fourier profile.  This is the exact
finite-coordinate mass occurring in the proved continuous convolution bound. -/
def coordinateX0Mass (u : ES → ComplexSpace) : ℝ :=
  ∑ i : Fin 3, ∫ ξ : ES, ‖u ξ i‖

/-- The sum of the three continuous coordinate `X⁻¹` masses. -/
def coordinateXm1Mass (u : ES → ComplexSpace) : ℝ :=
  ∑ i : Fin 3, normXm1 (fun ξ : ES => u ξ i)

/-- The sum of the three continuous coordinate `X¹` masses. -/
def coordinateX1Mass (u : ES → ComplexSpace) : ℝ :=
  ∑ i : Fin 3, normX1 (fun ξ : ES => u ξ i)

/-- Finite-coordinate aggregation of the continuous `X⁰` interpolation
estimate.  This is a genuine finite Cauchy--Schwarz step over the velocity
coordinates, not a lattice-frequency estimate. -/
theorem coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass
    (u : ES → ComplexSpace)
    (hxm1 : ∀ i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hx1 : ∀ i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖)) :
    coordinateX0Mass u ^ 2 ≤ coordinateXm1Mass u * coordinateX1Mass u := by
  unfold coordinateX0Mass coordinateXm1Mass coordinateX1Mass normXm1 normX1
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact integral_nonneg fun ξ =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro i hi
    exact integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro i hi
    exact Navier.Analysis.ContinuousLeiLinSpace.normX0_sq_le_normXm1_mul_normX1
      (fun ξ => u ξ i) (hxm1 i) (hx1 i)

/-- Spacetime `L¹` control of every coordinate gives the time integrability
of the coordinate `X⁰` mass by Fubini.  It deliberately does not assert
integrability of the square of that mass; the mixed time estimate needed for
the Duhamel fixed-point bound is a separate hypothesis. -/
theorem integrable_coordinateX0Mass_of_integrable_spacetime
    (u : ℝ → ES → ComplexSpace)
    (hu : ∀ i, Integrable (fun p : ℝ × ES => ‖u p.1 p.2 i‖)) :
    Integrable (fun t => coordinateX0Mass (u t)) := by
  unfold coordinateX0Mass
  apply integrable_finsetSum Finset.univ
  intro i hi
  exact (hu i).integral_prod_left

/-- The time-dependent continuous Duhamel operator.  The Bochner integral is
taken coordinatewise over the causal interval `[0,t]`; no regularity of this
operator is asserted merely from its definition. -/
def continuousDuhamel (ν : ℝ) (u v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ξ : ES) : ComplexSpace := fun i =>
  ∫ s in Icc (0 : ℝ) t,
    heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i) ξ

/-- Fixed-time source estimate in its sharp coordinate-mass form. -/
theorem normXm1_continuousNavierSource_le_coordinateX0Mass
    (u v : ℝ → ES → ComplexSpace) (t : ℝ)
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hv : ∀ s i, AEStronglyMeasurable (fun η : ES => v s η i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖)) :
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource u v t ξ)) ≤
      coordinateX0Mass (u t) * coordinateX0Mass (v t) := by
  unfold continuousNavierSource coordinateX0Mass
  calc
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierBilinear (u t) (v t) ξ)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∫ η : ES, ‖u t η j‖) * (∫ η : ES, ‖v t η i‖) :=
      ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_mass_le_of_aestronglyMeasurable
        (u t) (v t) (hu t) (hv t) (hu0 t) (hv0 t)
    _ = (∑ j : Fin 3, ∫ η : ES, ‖u t η j‖) *
          (∑ i : Fin 3, ∫ η : ES, ‖v t η i‖) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = coordinateX0Mass (u t) * coordinateX0Mass (v t) := rfl

/-- The genuine continuous time-bilinear estimate supplied by the established
measurable fixed-time symbol bound.  Its only time hypotheses are exactly the
integrability needed to compare the two set integrals. -/
theorem integral_normXm1_continuousNavierSource_le
    (u v : ℝ → ES → ComplexSpace) (s : Set ℝ)
    (hu : ∀ t j, AEStronglyMeasurable (fun η : ES => u t η j))
    (hv : ∀ t i, AEStronglyMeasurable (fun η : ES => v t η i))
    (hu0 : ∀ t j, Integrable (fun η : ES => ‖u t η j‖))
    (hv0 : ∀ t i, Integrable (fun η : ES => ‖v t η i‖))
    (hs : MeasurableSet s)
    (hsource : IntegrableOn (fun t => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u v t ξ)) s)
    (hmass : IntegrableOn (fun t => coordinateX0Mass (u t) *
      coordinateX0Mass (v t)) s) :
    (∫ t in s, ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u v t ξ)) ≤
      ∫ t in s, coordinateX0Mass (u t) * coordinateX0Mass (v t) := by
  exact setIntegral_mono_on hsource hmass hs
    (fun t ht => normXm1_continuousNavierSource_le_coordinateX0Mass
      u v t hu hv hu0 hv0)

/-- The diagonal time-bilinear source estimate after continuous coordinate
interpolation.  The two time-integrability hypotheses are explicit: Fubini
can establish first-moment coordinate mass integrability, whereas the square
and mixed endpoint product are the additional fixed-point inputs. -/
theorem integral_normXm1_continuousNavierSource_self_le_coordinateXm1X1
    (u : ℝ → ES → ComplexSpace) (s : Set ℝ)
    (hu : ∀ t j, AEStronglyMeasurable (fun η : ES => u t η j))
    (hu0 : ∀ t j, Integrable (fun η : ES => ‖u t η j‖))
    (hum1 : ∀ t j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u t η j‖))
    (hu1 : ∀ t j, Integrable (fun η : ES => ‖η‖ * ‖u t η j‖))
    (hs : MeasurableSet s)
    (hsource : IntegrableOn (fun t => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u u t ξ)) s)
    (h0sq : IntegrableOn (fun t => coordinateX0Mass (u t) ^ 2) s)
    (hmixed : IntegrableOn (fun t =>
      coordinateXm1Mass (u t) * coordinateX1Mass (u t)) s) :
    (∫ t in s, ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u u t ξ)) ≤
      ∫ t in s, coordinateXm1Mass (u t) * coordinateX1Mass (u t) := by
  calc
    (∫ t in s, ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u t ξ)) ≤
        ∫ t in s, coordinateX0Mass (u t) ^ 2 := by
      simpa [pow_two] using integral_normXm1_continuousNavierSource_le u u s
        hu hu hu0 hu0 hs hsource (by simpa [pow_two] using h0sq)
    _ ≤ ∫ t in s, coordinateXm1Mass (u t) * coordinateX1Mass (u t) := by
      exact setIntegral_mono_on h0sq hmixed hs (fun t ht =>
        coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass (u t)
          (hum1 t) (hu1 t))

/-! ## Checked obstruction to direct lattice sampling -/

/-- A profile supported at one continuous frequency.  It is useful for
separating Lebesgue-integral control from pointwise sampling. -/
def singletonFrequencyProfile (ξ₀ : ES) (z : ComplexSpace) : ES → ComplexSpace :=
  fun ξ => if ξ = ξ₀ then z else 0

@[simp] theorem singletonFrequencyProfile_at (ξ₀ : ES) (z : ComplexSpace) :
    singletonFrequencyProfile ξ₀ z ξ₀ = z := by
  simp [singletonFrequencyProfile]

theorem singletonFrequencyProfile_ae_zero (ξ₀ : ES) (z : ComplexSpace) :
    singletonFrequencyProfile ξ₀ z =ᵐ[volume] 0 := by
  filter_upwards [show ∀ᵐ ξ : ES, ξ ≠ ξ₀ by simp [ae_iff]] with ξ hξ
  simp [singletonFrequencyProfile, hξ]

@[simp] theorem coordinateXm1Mass_singletonFrequencyProfile
    (ξ₀ : ES) (z : ComplexSpace) :
    coordinateXm1Mass (singletonFrequencyProfile ξ₀ z) = 0 := by
  unfold coordinateXm1Mass normXm1
  apply Finset.sum_eq_zero
  intro i hi
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards [singletonFrequencyProfile_ae_zero ξ₀ z] with ξ hξ
  simp [hξ]

@[simp] theorem coordinateX1Mass_singletonFrequencyProfile
    (ξ₀ : ES) (z : ComplexSpace) :
    coordinateX1Mass (singletonFrequencyProfile ξ₀ z) = 0 := by
  unfold coordinateX1Mass normX1
  apply Finset.sum_eq_zero
  intro i hi
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards [singletonFrequencyProfile_ae_zero ξ₀ z] with ξ hξ
  simp [hξ]

/-- **Falsification of the direct continuous-to-lattice sampling route.**

No constant can control continuous-frequency point evaluation using only the
`X⁻¹` and `X¹` coordinate masses: Lebesgue integration forgets values on
singletons.  Thus the continuous mixed source estimate cannot be transported
to a lattice terminal coefficient by point sampling alone.  A valid bridge
would need additional regularity plus a proved sampling inequality, or a
measure-changing periodization theorem. -/
theorem not_pointwise_controlled_by_coordinateXm1X1 :
    ¬ ∃ C : ℝ, ∀ (u : ES → ComplexSpace) (ξ : ES) (j : Fin 3),
      ‖u ξ j‖ ≤ C * (coordinateXm1Mass u + coordinateX1Mass u) := by
  rintro ⟨C, hC⟩
  let z : ComplexSpace := fun _ => 1
  have h := hC (singletonFrequencyProfile 0 z) 0 0
  norm_num [z] at h

end Navier.Analysis.ContinuousLeiLinTimeDuhamel

#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.normXm1_continuousNavierSource_le_coordinateX0Mass
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.integral_normXm1_continuousNavierSource_le
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.integrable_coordinateX0Mass_of_integrable_spacetime
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.integral_normXm1_continuousNavierSource_self_le_coordinateXm1X1
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.singletonFrequencyProfile_ae_zero
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateXm1Mass_singletonFrequencyProfile
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateX1Mass_singletonFrequencyProfile
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.not_pointwise_controlled_by_coordinateXm1X1
