import Navier.Analysis.CriticalMildPathIntegrand

/-!
# Moving-tail control for the critical mild Duhamel integral

The changing observation-time integral separates into a common interval and
the literal tail below.  This file records the tail as an actual Bochner
integral with its explicit shifted heat majorant.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildObservationContinuity

open MeasureTheory Set
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand

/-- The literal moving observation-time tail, over the part of the later
interval not present at the earlier observation time. -/
def criticalMildDuhamelTail
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t t' : ℝ) : WeightedLatticeBanach :=
  ∫ s in Ioc t t', criticalMildPathIntegrand ν hν u hu t' s

/-- The moving tail is a genuine Bochner integral whenever the path has the
same radius control on the later horizon. -/
theorem integrableOn_criticalMildDuhamelTailIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t t' : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htt' : t ≤ t')
    (huR : ∀ s ∈ Ioc (0 : ℝ) t', ‖u s‖ ≤ R) :
    IntegrableOn (criticalMildPathIntegrand ν hν u hu t') (Ioc t t') volume := by
  have hfull := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR (le_trans ht htt') huR
  apply hfull.mono_set
  intro s hs
  exact ⟨lt_of_le_of_lt ht hs.1, hs.2⟩

/-- Norm control for the actual moving tail by the shifted singular scalar
majorant.  It exposes precisely the tail term needed in an observation-time
continuity proof. -/
theorem norm_criticalMildDuhamelTail_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t t' : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htt' : t ≤ t')
    (huR : ∀ s ∈ Ioc (0 : ℝ) t', ‖u s‖ ≤ R) :
    ‖criticalMildDuhamelTail ν hν u hu t t'‖ ≤
      ∫ s in Ioc t t', criticalMildPathMajorant ν R t' s := by
  have hactual := integrableOn_criticalMildDuhamelTailIntegrand
    ν hν u huc hu hR ht htt' huR
  have hscalarFull : IntegrableOn (criticalMildPathMajorant ν R t')
      (Ioc 0 t') volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans ht htt')).mp
      (intervalIntegrable_criticalMildPathMajorant ν R t')
  have hscalar : IntegrableOn (criticalMildPathMajorant ν R t')
      (Ioc t t') volume := by
    apply hscalarFull.mono_set
    intro s hs
    exact ⟨lt_of_le_of_lt ht hs.1, hs.2⟩
  have hmono : (fun s => ‖criticalMildPathIntegrand ν hν u hu t' s‖) ≤ᵐ[
      volume.restrict (Ioc t t')] criticalMildPathMajorant ν R t' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rcases hs.2.eq_or_lt with hst | hst
    · subst s
      simp [criticalMildPathIntegrand,
        positiveTimeHeatRegularizedSpectralOutput, criticalMildPathMajorant]
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    · exact norm_criticalMildPathIntegrand_le_of_norm_le
        ν hν u hu hR hst (huR s ⟨lt_of_le_of_lt ht hs.1, hst.le⟩)
  unfold criticalMildDuhamelTail
  calc
    ‖∫ s in Ioc t t', criticalMildPathIntegrand ν hν u hu t' s‖ ≤
        ∫ s in Ioc t t', ‖criticalMildPathIntegrand ν hν u hu t' s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc t t', criticalMildPathMajorant ν R t' s :=
      integral_mono_ae hactual.norm hscalar hmono

end Navier.Analysis.CriticalMildObservationContinuity

#print axioms Navier.Analysis.CriticalMildObservationContinuity.integrableOn_criticalMildDuhamelTailIntegrand
#print axioms Navier.Analysis.CriticalMildObservationContinuity.norm_criticalMildDuhamelTail_le
