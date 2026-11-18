import Navier.Analysis.ContinuousLeiLinFourierEndpointTrace
import Navier.Analysis.MildHorizonFreeRestartBarrier

noncomputable section
open MeasureTheory
open Navier.Analysis.ContinuousLeiLinSpace Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.FourierEndpointTrace
namespace Navier.Analysis.FourierEndpointBarrier
open Navier.Analysis.MildHorizonFreeRestartBarrier
/-- A single fixed integrable profile with a divergent first frequency moment.
It has the radial tail r⁻⁴ in three dimensions. At time zero the actual
nonlinear mild image reproduces this failure for every driving field. -/
theorem raw_X0_data_has_no_endpoint_X1 (ν : ℝ) (hν : 0 < ν) :
    ∃ a : ES → ComplexSpace,
      (∀ i : Fin 3, Integrable (fun ξ : ES => a ξ i)) ∧
      ∀ u : ℝ → ES → ComplexSpace,
        ¬ Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousMildImage ν hν a u 0 ξ 0‖) := by
  let a : ES → ComplexSpace := fun ξ _ => (‖ξ‖ : ℂ) * mildBarrierProfile ξ
  have hnorm (ξ : ES) (i : Fin 3) : ‖a ξ i‖ = ‖ξ‖ * ‖mildBarrierProfile ξ‖ := by
    simp [a]
  refine ⟨a, ?_, ?_⟩
  · intro i
    have hm : Measurable (fun ξ : ES => a ξ i) := by
      exact (Complex.continuous_ofReal.measurable.comp continuous_norm.measurable).mul
        (Complex.continuous_ofReal.measurable.comp measurable_mildBarrierScalar)
    apply (integrable_norm_iff hm.aestronglyMeasurable).mp
    simpa only [hnorm] using integrable_barrier_X1
  · intro u hi
    rw [mild_initial_trace] at hi
    apply not_integrable_barrier_X2
    simpa only [hnorm, pow_two, mul_assoc] using hi
#print axioms raw_X0_data_has_no_endpoint_X1
end Navier.Analysis.FourierEndpointBarrier
