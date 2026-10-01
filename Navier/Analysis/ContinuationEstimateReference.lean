import Navier.Analysis.ContinuousLeiLinSelfMap

/-!
# Independent reference for the quadratic mild continuation estimate

This module freezes the exact estimate immediately before the smallness
condition in `continuousMildImage_self_map_ball`.  It keeps the existing
continuous Fourier carrier, its `X⁻¹` and time-integrated `X¹` ball bounds,
the prefix integrability hypotheses, and the proved B1/D3 estimates.  It omits
only `R ≤ ν / 16` and therefore records the unsimplified quadratic output.

No fixed-point, continuation, or global-regularity conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Navier.Analysis.ContinuationEstimateReference

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap

/-- Exact quadratic precursor to the `7/4` self-map estimate.  The two
conclusions retain the full `R + 12 ν⁻¹ R²` dependence before any
smallness assumption is used. -/
def ExactQuadraticContinuationEstimate : Prop :=
  ∀ (ν R T : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace),
    coordinateXm1Mass a ≤ R →
    (∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ (2 : ℝ) * R) →
    (∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s)) ≤ (2 : ℝ) * ν⁻¹ * R →
    (∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume) →
    (∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume) →
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s)) →
    ((∫ t in Icc (0 : ℝ) T,
      coordinateX1Mass (continuousMildImage ν hν a u t)) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s)) →
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
        R + (12 : ℝ) * ν⁻¹ * R ^ 2) ∧
      (∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage ν hν a u t)) ≤
          ν⁻¹ * (R + (12 : ℝ) * ν⁻¹ * R ^ 2)

end Navier.Analysis.ContinuationEstimateReference
