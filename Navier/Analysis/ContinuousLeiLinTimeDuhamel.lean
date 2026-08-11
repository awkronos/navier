import Navier.Analysis.ContinuousLeiLinSpace

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

end Navier.Analysis.ContinuousLeiLinTimeDuhamel

#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.normXm1_continuousNavierSource_le_coordinateX0Mass
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.integral_normXm1_continuousNavierSource_le
