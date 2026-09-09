import Navier.Analysis.PhysicalPeriodicHighTailFlux
import Navier.Analysis.CriticalMildLocalUniformBootstrap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.RawHighEnergyDifferentiation

open Set Filter Navier
open scoped Topology
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildLocalUniformBootstrap
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicHighTailFlux

/-- Derivative of squared raw decoded modal amplitude; kinetic energy uses
the separate factor `1 / (2 * (2π)^2)` in period-one physical units. -/
def rawModeEnergyRate (A : WeightedLatticeBanach)
    (D : LatticeMode → ComplexSpace) (k : LatticeMode) : ℝ :=
  2 * inner ℝ (complexEuclideanPoint (weightedLatticeCoefficient A k))
    (complexEuclideanPoint (D k))

theorem hasDerivAt_rawModeEnergy
    (A : ℝ → WeightedLatticeBanach) (D : LatticeMode → ComplexSpace)
    (t : ℝ) (k : LatticeMode)
    (h : ∀ i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i) (D k i) t) :
    HasDerivAt (fun r => rawSpectralEnergyDensity (A r) k)
      (rawModeEnergyRate (A t) D k) t := by
  let L : (Fin 3 → ℂ) →L[ℝ] ComplexE3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap
  have hp : HasDerivAt (fun r => weightedLatticeCoefficient (A r) k) (D k) t := by
    rw [hasDerivAt_pi]
    exact h
  have hv := L.hasFDerivAt.comp_hasDerivAt t hp
  exact hv.norm_sq

theorem abs_rawModeEnergyRate_le
    (A : WeightedLatticeBanach) (D : LatticeMode → ComplexSpace) (k : LatticeMode) :
    |rawModeEnergyRate A D k| ≤
      2 * complexEuclideanNorm (weightedLatticeCoefficient A k) * complexEuclideanNorm (D k) := by
  unfold rawModeEnergyRate
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa [complexEuclideanNorm, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm
        (complexEuclideanPoint (weightedLatticeCoefficient A k))
        (complexEuclideanPoint (D k))) (by norm_num : (0 : ℝ) ≤ 2)

theorem decoded_amplitude_le_high_cutoff
    (A : WeightedLatticeBanach) {N : ℝ} (hN : 0 ≤ N)
    (k : LatticeMode) (hk : N ≤ latticeModeSize k) :
    complexEuclideanNorm (weightedLatticeCoefficient A k) ≤ ‖A‖ / (1 + N) := by
  have heval := norm_weightedLattice_eval_le A k
  rw [← latticeWeightedAmplitude_coefficient A k] at heval
  apply (le_div_iff₀ (by positivity : 0 < 1 + N)).2
  have hp := mul_le_mul_of_nonneg_right (add_le_add_left hk 1)
    (norm_nonneg (complexEuclideanPoint (weightedLatticeCoefficient A k)))
  have hp' : (1 + N) * complexEuclideanNorm (weightedLatticeCoefficient A k) ≤
      latticeModeWeight k * complexEuclideanNorm (weightedLatticeCoefficient A k) := by
    simpa [latticeModeWeight, latticeModeSize, complexEuclideanNorm, add_comm] using hp
  simpa [mul_comm] using hp'.trans heval

def rawHighModeEnergyRate (N : ℝ) (A : WeightedLatticeBanach)
    (D : LatticeMode → ComplexSpace) (k : LatticeMode) : ℝ :=
  if N ≤ latticeModeSize k then rawModeEnergyRate A D k else 0

theorem abs_rawHighModeEnergyRate_le
    (A : WeightedLatticeBanach) (D : LatticeMode → ComplexSpace)
    {N : ℝ} (hN : 0 ≤ N) (k : LatticeMode) :
    |rawHighModeEnergyRate N A D k| ≤
      (2 * ‖A‖ / (1 + N)) * complexEuclideanNorm (D k) := by
  unfold rawHighModeEnergyRate
  split_ifs with hk
  · calc
      |rawModeEnergyRate A D k| ≤
          2 * complexEuclideanNorm (weightedLatticeCoefficient A k) *
            complexEuclideanNorm (D k) := abs_rawModeEnergyRate_le A D k
      _ ≤ 2 * (‖A‖ / (1 + N)) * complexEuclideanNorm (D k) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (decoded_amplitude_le_high_cutoff A hN k hk)
            (by norm_num)) (norm_nonneg _)
      _ = _ := by ring
  · simp only [abs_zero]
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (norm_nonneg _)

/-- An absolutely summable mode derivative gives a quantitative energy-rate
tail, with an extra inverse cutoff supplied by the actual weighted carrier. -/
theorem tsum_abs_rawHighModeEnergyRate_le
    (A : WeightedLatticeBanach) (D : LatticeMode → ComplexSpace)
    (hD : Summable fun k => complexEuclideanNorm (D k)) {N : ℝ} (hN : 0 ≤ N) :
    (Summable (rawHighModeEnergyRate N A D)) ∧
    (∑' k, |rawHighModeEnergyRate N A D k|) ≤
      (2 * ‖A‖ / (1 + N)) * (∑' k, complexEuclideanNorm (D k)) := by
  have hmajor := hD.mul_left (2 * ‖A‖ / (1 + N))
  have hs : Summable (rawHighModeEnergyRate N A D) := by
    apply hmajor.of_norm_bounded
    intro k
    simpa only [Real.norm_eq_abs] using abs_rawHighModeEnergyRate_le A D hN k
  refine ⟨hs, ?_⟩
  calc
    (∑' k, |rawHighModeEnergyRate N A D k|) ≤
        ∑' k, (2 * ‖A‖ / (1 + N)) * complexEuclideanNorm (D k) :=
      hs.abs.tsum_le_tsum (abs_rawHighModeEnergyRate_le A D hN) hmajor
    _ = _ := tsum_mul_left

theorem hasDerivAt_rawHighModeEnergy
    (A : ℝ → WeightedLatticeBanach) (D : LatticeMode → ComplexSpace)
    (t : ℝ) (k : LatticeMode) (N : ℝ)
    (h : ∀ i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i) (D k i) t) :
    HasDerivAt (fun r => if N ≤ latticeModeSize k then rawSpectralEnergyDensity (A r) k else 0)
      (rawHighModeEnergyRate N (A t) D k) t := by
  by_cases hk : N ≤ latticeModeSize k
  · simpa only [hk, if_true, rawHighModeEnergyRate] using hasDerivAt_rawModeEnergy A D t k h
  · simpa only [hk, if_false, rawHighModeEnergyRate] using (hasDerivAt_const t (0 : ℝ))

theorem latticeMode_norm_le_size (k : LatticeMode) : ‖k‖ ≤ latticeModeSize k := by
  have h0 := PiLp.norm_apply_le (complexFrequency (latticeFrequency k)) (0 : Fin 3)
  have h1 := PiLp.norm_apply_le (complexFrequency (latticeFrequency k)) (1 : Fin 3)
  have h2 := PiLp.norm_apply_le (complexFrequency (latticeFrequency k)) (2 : Fin 3)
  rw [Prod.norm_def, Prod.norm_def]
  apply max_le
  · simpa [latticeModeSize, complexFrequency, complexEuclideanPoint,
      complexOfReal, latticeFrequency, Int.norm_eq_abs] using h0
  · apply max_le
    · simpa [latticeModeSize, complexFrequency, complexEuclideanPoint,
        complexOfReal, latticeFrequency, Int.norm_eq_abs] using h1
    · simpa [latticeModeSize, complexFrequency, complexEuclideanPoint,
        complexOfReal, latticeFrequency, Int.norm_eq_abs] using h2

theorem finite_low_modes (N : ℝ) : {k : LatticeMode | latticeModeSize k ≤ N}.Finite := by
  have hball : (Metric.closedBall (0 : LatticeMode) N).Finite :=
    (isCompact_closedBall (0 : LatticeMode) N).finite
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  apply hball.subset
  intro k hk
  simpa [Metric.mem_closedBall, dist_zero_right] using (latticeMode_norm_le_size k).trans hk

theorem rawEnergyRate_finite_sum_error_le
    (A : WeightedLatticeBanach) (D : LatticeMode → ComplexSpace)
    (hD : Summable fun k => complexEuclideanNorm (D k))
    {N K : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K) (F : Finset LatticeMode)
    (hF : ∀ k, latticeModeSize k ≤ K → k ∈ F) :
    |(∑' k, rawHighModeEnergyRate N A D k) - ∑ k ∈ F, rawHighModeEnergyRate N A D k| ≤
      (2 * ‖A‖ / (1 + K)) * (∑' k, complexEuclideanNorm (D k)) := by
  classical
  let f := rawHighModeEnergyRate N A D
  have hf := (tsum_abs_rawHighModeEnergyRate_le A D hD hN).1
  have hsub := hf.subtype (fun k => k ∈ (↑F : Set LatticeMode)ᶜ)
  have hDsub := hD.subtype (fun k => k ∈ (↑F : Set LatticeMode)ᶜ)
  have hpoint : ∀ k : ↑((↑F : Set LatticeMode)ᶜ),
      |f k| ≤ (2 * ‖A‖ / (1 + K)) * complexEuclideanNorm (D k) := by
    intro k
    have hk : K ≤ latticeModeSize k := (lt_of_not_ge (fun h => k.2 (hF k h))).le
    by_cases hn : N ≤ latticeModeSize k
    · simpa only [f, rawHighModeEnergyRate, hn, hk, if_true] using
        abs_rawHighModeEnergyRate_le A D hK k
    · simp only [f, rawHighModeEnergyRate, hn, if_false, abs_zero]
      exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (norm_nonneg _)
  have hsplit := hf.sum_add_tsum_compl (s := F)
  have heq : (∑' k, f k) - ∑ k ∈ F, f k = ∑' k : ↑((↑F : Set LatticeMode)ᶜ), f k := by
    simpa only [f, add_sub_cancel_left]
      using congrArg (fun z => z - ∑ k ∈ F, f k) hsplit.symm
  change |(∑' k, f k) - ∑ k ∈ F, f k| ≤ _
  rw [heq]
  calc
    |∑' k : ↑((↑F : Set LatticeMode)ᶜ), f k| ≤
        ∑' k : ↑((↑F : Set LatticeMode)ᶜ), |f k| := by
      simpa only [f, Function.comp_def, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsub.norm
    _ ≤ ∑' k : ↑((↑F : Set LatticeMode)ᶜ),
        (2 * ‖A‖ / (1 + K)) * complexEuclideanNorm (D k) :=
      hsub.abs.tsum_le_tsum hpoint (hDsub.mul_left _)
    _ = (2 * ‖A‖ / (1 + K)) *
        ∑' k : ↑((↑F : Set LatticeMode)ᶜ), complexEuclideanNorm (D k) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.tsum_subtype_le (fun k => complexEuclideanNorm (D k))
        (↑F : Set LatticeMode)ᶜ (fun _ => norm_nonneg _) hD) (by positivity)

/-- Uniform total derivative mass suffices here: the weighted velocity supplies
an additional inverse frequency in the energy derivative tail. -/
theorem tendstoUniformlyOn_rawEnergyRate_finite_sums
    (A : ℝ → WeightedLatticeBanach) (D : ℝ → LatticeMode → ComplexSpace)
    (s : Set ℝ) {N R M : ℝ} (hN : 0 ≤ N) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hA : ∀ t ∈ s, ‖A t‖ ≤ R)
    (hD : ∀ t ∈ s, Summable fun k => complexEuclideanNorm (D t k))
    (hDM : ∀ t ∈ s, (∑' k, complexEuclideanNorm (D t k)) ≤ M) :
    TendstoUniformlyOn
      (fun F : Finset LatticeMode => fun t => ∑ k ∈ F, rawHighModeEnergyRate N (A t) (D t) k)
      (fun t => ∑' k, rawHighModeEnergyRate N (A t) (D t) k) atTop s := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let K : ℝ := 2 * R * M / ε
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let F₀ := (finite_low_modes K).toFinset
  filter_upwards [eventually_ge_atTop F₀] with F hF t ht
  have hcontains : ∀ k, latticeModeSize k ≤ K → k ∈ F := by
    intro k hk
    apply hF
    exact (finite_low_modes K).mem_toFinset.mpr hk
  rw [Real.dist_eq]
  calc
    _ ≤ (2 * ‖A t‖ / (1 + K)) * (∑' k, complexEuclideanNorm (D t k)) :=
      rawEnergyRate_finite_sum_error_le (A t) (D t) (hD t ht) hN hK F hcontains
    _ ≤ (2 * R / (1 + K)) * M := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (by nlinarith [hA t ht]) (by positivity)
      · exact hDM t ht
      · exact tsum_nonneg (fun _ => norm_nonneg _)
      · positivity
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 1 + K)]
      have hcancel : ε * K = 2 * R * M := by
        dsimp [K]
        field_simp
      nlinarith

/-- Differentiation of the genuine countable high-frequency energy. The
hypotheses concern mode derivatives and uniform total mass, not the conclusion. -/
theorem hasDerivAt_rawHighSpectralEnergy_of_uniform_mass
    (A : ℝ → WeightedLatticeBanach) (D : ℝ → LatticeMode → ComplexSpace)
    {s : Set ℝ} (hs : IsOpen s) {N R M t : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hM : 0 ≤ M) (ht : t ∈ s)
    (hA : ∀ r ∈ s, ‖A r‖ ≤ R)
    (hD : ∀ r ∈ s, Summable fun k => complexEuclideanNorm (D r k))
    (hDM : ∀ r ∈ s, (∑' k, complexEuclideanNorm (D r k)) ≤ M)
    (hderiv : ∀ r ∈ s, ∀ k i,
      HasDerivAt (fun q => weightedLatticeCoefficient (A q) k i) (D r k i) r) :
    HasDerivAt (fun r => rawHighSpectralEnergy N (A r))
      (∑' k, rawHighModeEnergyRate N (A t) (D t) k) t := by
  classical
  apply hasDerivAt_of_tendstoUniformlyOn hs
    (tendstoUniformlyOn_rawEnergyRate_finite_sums A D s hN hR hM hA hD hDM)
  · apply Filter.Eventually.of_forall
    intro F r hr
    exact HasDerivAt.sum (fun k _ => hasDerivAt_rawHighModeEnergy A (D r) r k N (hderiv r hr k))
  · intro r _
    simpa only [Finset.sum_apply, rawHighSpectralEnergy, HasSum,
      SummationFilter.unconditional_filter] using
      (summable_rawHighSpectralEnergy N (A r)).hasSum
  · exact ht

end Navier.Analysis.RawHighEnergyDifferentiation
