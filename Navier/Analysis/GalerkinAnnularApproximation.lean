import Navier.Analysis.GalerkinUniformBandAssembly
import Mathlib.Data.Int.Log

/-! Open dyadic Fourier bands cover Euclidean space up to a null set. -/

noncomputable section
open MeasureTheory

namespace Navier.Analysis.GalerkinAnnularApproximation

open DivFreeGradientEnstrophy

def dyadicAnnulus (k : ℤ) : Set EuclSpace :=
  {ξ | (2 : ℝ) ^ k < ‖ξ‖ ∧ ‖ξ‖ < (2 : ℝ) ^ (k + 1)}

theorem dyadicAnnulus_isOpen (k : ℤ) : IsOpen (dyadicAnnulus k) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem dyadicAnnulus_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (dyadicAnnulus i) (dyadicAnnulus j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ξ hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hm : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hi.2.le.trans hm)) hj.1
  · have hm : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hj.2.le.trans hm)) hi.1

theorem mem_dyadicAnnulus_of_norm_ne_zpow (ξ : EuclSpace) (hξ : ξ ≠ 0)
    (hboundary : ∀ k : ℤ, ‖ξ‖ ≠ (2 : ℝ) ^ k) :
    ξ ∈ dyadicAnnulus (Int.log 2 ‖ξ‖) := by
  have hlo := Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ))
    (norm_pos_iff.mpr hξ)
  have hhi := Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) ‖ξ‖
  exact ⟨lt_of_le_of_ne hlo (hboundary _).symm, hhi⟩

theorem ae_mem_iUnion_dyadicAnnulus :
    ∀ᵐ ξ : EuclSpace, ξ ∈ ⋃ k : ℤ, dyadicAnnulus k := by
  have hsphere (k : ℤ) :
      ∀ᵐ ξ : EuclSpace, ‖ξ‖ ≠ (2 : ℝ) ^ k := by
    apply ae_iff.mpr
    simpa [Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (volume : Measure EuclSpace) 0 ((2 : ℝ) ^ k)
  have hzero : ∀ᵐ ξ : EuclSpace, ξ ≠ 0 := by
    apply ae_iff.mpr
    simpa using (measure_singleton (μ := (volume : Measure EuclSpace)) 0)
  filter_upwards [hzero, ae_all_iff.mpr hsphere] with ξ hξ hboundary
  exact Set.mem_iUnion.mpr
    ⟨Int.log 2 ‖ξ‖, mem_dyadicAnnulus_of_norm_ne_zpow ξ hξ hboundary⟩

/-- Every integrable density splits over the actual open bands. Their omitted
dyadic spheres and the origin have zero Lebesgue measure. -/
theorem integral_eq_tsum_dyadicAnnulus {f : EuclSpace → ℝ}
    (hf : Integrable f) :
    (∫ ξ, f ξ) = ∑' k : ℤ, ∫ ξ in dyadicAnnulus k, f ξ := by
  have heq : (⋃ k : ℤ, dyadicAnnulus k) =ᵐ[volume] Set.univ := by
    filter_upwards [ae_mem_iUnion_dyadicAnnulus] with ξ hξ
    exact propext (iff_of_true hξ (Set.mem_univ ξ))
  have hi := integral_iUnion (fun k => (dyadicAnnulus_isOpen k).measurableSet)
    dyadicAnnulus_pairwise_disjoint hf.integrableOn
  rw [setIntegral_congr_set heq, setIntegral_univ] at hi
  exact hi

def bandWindow (n : ℕ) : Set EuclSpace :=
  ⋃ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), dyadicAnnulus k

theorem bandWindow_isOpen (n : ℕ) : IsOpen (bandWindow n) :=
  isOpen_iUnion (fun k => isOpen_iUnion fun _ => dyadicAnnulus_isOpen k)

/-- Finite dyadic windows exhaust any integrable Fourier energy. This is the
tail estimate for the subsequent smooth approximation inside each open band. -/
theorem tendsto_integral_bandWindow {f : EuclSpace → ℝ} (hf : Integrable f) :
    Filter.Tendsto (fun n : ℕ => ∫ ξ in bandWindow n, f ξ)
      Filter.atTop (nhds (∫ ξ, f ξ)) := by
  have hlim : ∀ᵐ ξ : EuclSpace,
      Filter.Tendsto (fun n : ℕ => (bandWindow n).indicator f ξ)
        Filter.atTop (nhds (f ξ)) := by
    filter_upwards [ae_mem_iUnion_dyadicAnnulus] with ξ hξ
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hξ
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop k.natAbs] with n hn
    have hkn : k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      rw [Finset.mem_Icc]
      have hle : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
      have hneg : -k ≤ (k.natAbs : ℤ) := by
        simpa using (show -k ≤ ((-k).natAbs : ℤ) from Int.le_natAbs)
      constructor <;> omega
    have hmem : ξ ∈ bandWindow n :=
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkn, hk⟩⟩
    simp [hmem]
  have hdom := tendsto_integral_of_dominated_convergence
    (bound := fun ξ => ‖f ξ‖)
    (fun n => hf.aestronglyMeasurable.indicator
      (bandWindow_isOpen n).measurableSet)
    hf.norm
    (fun n => Filter.Eventually.of_forall fun ξ => by
      by_cases h : ξ ∈ bandWindow n <;> simp [h]) hlim
  simpa only [integral_indicator (bandWindow_isOpen _).measurableSet] using hdom

end Navier.Analysis.GalerkinAnnularApproximation
