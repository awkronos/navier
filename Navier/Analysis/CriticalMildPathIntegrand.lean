import Navier.Analysis.CriticalMildHeatFlow

/-!
# Time-dependent critical mild Duhamel integrand

The earlier completed Bochner integral accepts two fixed carrier elements.
The mild equation instead evaluates the nonlinear transport on the evolving
path at the integration time.  This file introduces that literal object and
connects it to the already checked inverse-square-root estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildPathIntegrand

open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildDuhamelBochner

/-- The literal path-dependent nonlinear integrand at observation time `t`
and integration time `s`, with heat lag `t-s`. -/
def criticalMildPathIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s : ℝ) : WeightedLatticeBanach :=
  positiveTimeHeatRegularizedSpectralOutput ν hν
    (u s) (u s) (hu s) (t - s)

/-- Before the observation time, the actual path-dependent integrand obeys
the checked inverse-square-root heat-lag majorant. -/
theorem norm_criticalMildPathIntegrand_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ ^ 2 := by
  unfold criticalMildPathIntegrand
  have hlag : 0 < t - s := sub_pos.mpr hst
  have h := norm_positiveTimeHeatRegularizedSpectralOutput_le
    ν hν (u s) (u s) (hu s) hlag
  calc
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν
        (u s) (u s) (hu s) (t - s)‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ * ‖u s‖ := by
        simpa [duhamelHeatTimeMajorant] using h
    _ = (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ ^ 2 := by
      ring

/-- A uniform radius bound on the evolving path gives the corresponding
quadratic heat-lag majorant. -/
theorem norm_criticalMildPathIntegrand_le_of_norm_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t s : ℝ} (hR : 0 ≤ R) (hst : s < t)
    (huR : ‖u s‖ ≤ R) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2 := by
  have hbase := norm_criticalMildPathIntegrand_le ν hν u hu hst
  have hcoef :
      0 ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) := by
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
  exact hbase.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) hR).2 huR) hcoef)

end Navier.Analysis.CriticalMildPathIntegrand

#print axioms Navier.Analysis.CriticalMildPathIntegrand.norm_criticalMildPathIntegrand_le
#print axioms Navier.Analysis.CriticalMildPathIntegrand.norm_criticalMildPathIntegrand_le_of_norm_le
