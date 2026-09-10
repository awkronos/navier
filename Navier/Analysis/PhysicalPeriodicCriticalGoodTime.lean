import Navier.Analysis.PhysicalPeriodicGoodTimeSelection
import Navier.Analysis.LatticeCriticalDissipationKernel

/-!
# Direct critical control at dissipation-selected times

The homogeneous inverse-frequency norm is controlled by quadratic dissipation
on the three-dimensional periodic lattice. This estimate concerns the actual
state, without a free heat-evolution lag.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PhysicalPeriodicCriticalGoodTime

open Navier Set
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicGoodTimeSelection
open Navier.Analysis.LatticeCriticalDissipationKernel

private theorem tsum_mul_le_sqrt_squares {ι : Type*} (f g : ι → ℝ)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Summable fun k => f k ^ 2) (hg : Summable fun k => g k ^ 2) :
    (∑' k, f k * g k) ≤
      Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  apply Real.tsum_le_of_sum_le (fun k => mul_nonneg (hf0 k) (hg0 k))
  intro s
  refine (Real.sum_mul_le_sqrt_mul_sqrt s f g).trans ?_
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (hf.sum_le_tsum s (fun k _ => sq_nonneg (f k)))
  · exact Real.sqrt_le_sqrt (hg.sum_le_tsum s (fun k _ => sq_nonneg (g k)))
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

/-- The exact homogeneous inverse-frequency norm is controlled directly by
the state's dissipation, with a finite, datum-independent lattice constant. -/
theorem normXm1_offZero_le_sqrt_dissipation
    (u : WeightedLatticeBanach) :
    normXm1 latticeModeSize (amplitudeOffZero u) ≤
      Real.sqrt (∑' k : LatticeMode,
        if k = 0 then (0 : ℝ) else (latticeModeSize k ^ 4)⁻¹) *
      Real.sqrt (rawHighSpectralDissipation 0 u) := by
  let f : LatticeMode → ℝ := fun k =>
    if k = 0 then 0 else (latticeModeSize k ^ 2)⁻¹
  let g : LatticeMode → ℝ := fun k => latticeModeSize k * weightedAmplitude u k
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    split_ifs <;> positivity
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    mul_nonneg (latticeModeSize_nonneg k) (weightedAmplitude_nonneg u k)
  have hfsq : ∀ k, f k ^ 2 =
      if k = 0 then 0 else (latticeModeSize k ^ 4)⁻¹ := by
    intro k
    dsimp [f]
    split_ifs
    · norm_num
    · rw [← inv_pow]
      ring
  have hgsq : ∀ k, g k ^ 2 = rawSpectralDissipationDensity u k := by
    intro k
    simp only [g, rawSpectralDissipationDensity, mul_pow]
  have hf : Summable fun k => f k ^ 2 :=
    summable_inverseFourthKernel.congr (fun k => (hfsq k).symm)
  have hg : Summable fun k => g k ^ 2 :=
    (summable_rawSpectralDissipationDensity u).congr (fun k => (hgsq k).symm)
  have hfg : ∀ k, f k * g k =
      (latticeModeSize k)⁻¹ * |amplitudeOffZero u k| := by
    intro k
    by_cases hk : k = 0
    · simp [f, amplitudeOffZero, hk]
    · have hs : latticeModeSize k ≠ 0 :=
        ne_of_gt (zero_lt_one.trans_le (one_le_latticeModeSize_of_ne_zero hk))
      simp only [f, g, if_neg hk, amplitudeOffZero,
        abs_of_nonneg (weightedAmplitude_nonneg u k)]
      field_simp
  have h := tsum_mul_le_sqrt_squares f g hf0 hg0 hf hg
  simpa only [hfg, hfsq, hgsq, normXm1, wNorm,
    rawHighSpectralDissipation, if_pos (latticeModeSize_nonneg _)] using h

/-- Every nondegenerate existing physical mild window has a time with
datum-only inverse-frequency control. The bound contains neither the chart
radius nor a positive heat lag. It does not assume that the window exists
beyond the lifespan of the solution. -/
theorem exists_criticalGoodTime
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ < t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    ∃ c ∈ Icc δ t,
      normXm1 latticeModeSize (amplitudeOffZero (A c)) ≤
        Real.sqrt (∑' k : LatticeMode,
          if k = 0 then (0 : ℝ) else (latticeModeSize k ^ 4)⁻¹) *
        Real.sqrt (rawHighSpectralEnergy 0 a / (2 * μ * (t - δ))) := by
  obtain ⟨c, hc, hDc⟩ := exists_goodDissipationTime μ hμ a ha A hAc
    hdiv hreal hR hδ hδt htT hbound hmild
  refine ⟨c, hc, (normXm1_offZero_le_sqrt_dissipation (A c)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hμ) (sub_pos.mpr hδt))).2
  simpa only [mul_comm] using hDc

end Navier.Analysis.PhysicalPeriodicCriticalGoodTime
