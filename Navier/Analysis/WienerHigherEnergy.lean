import Navier.Analysis.WienerEnergy

/-!
# Weighted Fourier energies of a Wiener piece (damped `Hˢ` estimate, step 1)

For the pointwise mild solution `w` of a Wiener piece and every `k : ℕ`, the weighted
energy `E_k(t) = ∫ ‖ξ‖^{2k} ∑ᵢ |wᵢ(t,ξ)|² dξ` is continuous on `[0,T]` and
differentiable on `(0,T)` with

`E_k'(t) = -2ν E_{k+1}(t) + 2 Re ∫ ‖ξ‖^{2k} ∑ᵢ Bilᵢ(w,w)(t,ξ) conj wᵢ(t,ξ) dξ`

(`hasDerivAt_EWk`, `continuousOn_EWk`).  The first term is the dissipation; the second
is the trilinear term, which vanishes for `k = 0` (`WienerEnergy.integral_bil_conj_eq_zero`)
but not for `k ≥ 1`.  Its bound by `‖∇u‖∞ E_k` is step 2 of the damped estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace Navier.Analysis.WienerHigherEnergy

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerEnergy
open Navier.Analysis.WienerPhysicalPDE

/-- The weighted energy density `‖ξ‖^{2k} ∑ᵢ |wᵢ|²`. -/
def eWk (k : ℕ) (w : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ℝ := ‖ξ‖ ^ (2 * k) * eW w t ξ

/-- The weighted Fourier energy `E_k`. -/
def EWk (k : ℕ) (w : ℝ → ES → ComplexSpace) (t : ℝ) : ℝ := ∫ ξ, eWk k w t ξ

/-- The weighted trilinear term. -/
def TWk (k : ℕ) (w : ℝ → ES → ComplexSpace) (t : ℝ) : ℂ :=
  ∫ ξ, (‖ξ‖ ^ (2 * k) : ℝ) * ∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)

/-- A moment-weighted majorant turned real is integrable. -/
theorem integrable_weight_toReal {M : ES → ℝ≥0∞} (hM : Measurable M)
    (hmom : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * M ξ ≠ ⊤) (n : ℕ) :
    Integrable (fun ξ => ‖ξ‖ ^ n * (M ξ).toReal) := by
  have h := integrable_toReal_of_lintegral_ne_top
    ((ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul hM).aemeasurable
    (hmom n)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  show (ENNReal.ofReal (‖ξ‖ ^ n) * M ξ).toReal = ‖ξ‖ ^ n * (M ξ).toReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

variable {ν T : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace) {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w) {R : ℝ} (hR0 : 0 ≤ R)
  (hRb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖w t ξ‖ ≤ R)

include hν hG hRb in
theorem weighted_bounds (k : ℕ) :
    ∃ Bd : ES → ℝ, Integrable Bd ∧ ∃ Bd' : ES → ℝ, Integrable Bd' ∧
      (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, |eWk k w t ξ| ≤ Bd ξ) ∧
      (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T,
        |‖ξ‖ ^ (2 * k) * dW ν w t ξ| ≤ Bd' ξ) := by
  obtain ⟨-, M1, hM1, hb1, hmom1, -⟩ := good_W hν.le hG 1
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hG
  have hMt : ∀ᵐ ξ ∂(volume : Measure ES), M ξ < ⊤ :=
    ae_lt_top hM (lintegral_ne_top_of_mom hmom)
  have hM1t : ∀ᵐ ξ ∂(volume : Measure ES), M1 ξ < ⊤ :=
    ae_lt_top hM1 (lintegral_ne_top_of_mom hmom1)
  refine ⟨fun ξ => 3 * R * (‖ξ‖ ^ (2 * k) * (M ξ).toReal),
    (integrable_weight_toReal hM hmom _).const_mul _,
    fun ξ => 6 * R * (‖ξ‖ ^ (2 * k) * (M1 ξ).toReal),
    (integrable_weight_toReal hM1 hmom1 _).const_mul _, ?_, ?_⟩
  · filter_upwards [hb, hRb, hMt] with ξ h1 h2 h3 t ht
    have hR : 0 ≤ R := (norm_nonneg _).trans (h2 t ht)
    unfold eWk
    rw [abs_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity))]
    have := (eW_le (h2 t ht)).trans (mul_le_mul_of_nonneg_left
      (norm_le_toReal_of_enorm_le h3.ne (h1 t ht)) (by positivity : (0 : ℝ) ≤ 3 * R))
    calc ‖ξ‖ ^ (2 * k) * eW w t ξ ≤ ‖ξ‖ ^ (2 * k) * (3 * R * (M ξ).toReal) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · filter_upwards [hb1, hRb, hM1t] with ξ h1 h2 h3 t ht
    have hR : 0 ≤ R := (norm_nonneg _).trans (h2 t ht)
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hd : |dW ν w t ξ| ≤ 6 * R * (M1 ξ).toReal := by
      unfold dW
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hi : ∀ i : Fin 3, |2 * (W ν w 1 t ξ i * conj (w t ξ i)).re| ≤
          2 * R * (M1 ξ).toReal := by
        intro i
        rw [abs_mul, abs_two]
        have hre : |(W ν w 1 t ξ i * conj (w t ξ i)).re| ≤ R * (M1 ξ).toReal := by
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, Complex.norm_conj]
          calc ‖W ν w 1 t ξ i‖ * ‖w t ξ i‖ ≤ (M1 ξ).toReal * R :=
                mul_le_mul ((norm_le_pi_norm _ i).trans
                  (norm_le_toReal_of_enorm_le h3.ne (h1 t ht)))
                  ((norm_le_pi_norm _ i).trans (h2 t ht)) (norm_nonneg _) ENNReal.toReal_nonneg
            _ = R * (M1 ξ).toReal := by ring
        linarith
      calc ∑ i : Fin 3, |2 * (W ν w 1 t ξ i * conj (w t ξ i)).re|
          ≤ ∑ _i : Fin 3, 2 * R * (M1 ξ).toReal := Finset.sum_le_sum fun i _ => hi i
        _ = 6 * R * (M1 ξ).toReal := by simp; ring
    calc ‖ξ‖ ^ (2 * k) * |dW ν w t ξ| ≤ ‖ξ‖ ^ (2 * k) * (6 * R * (M1 ξ).toReal) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring

include hG in
theorem measurable_eWk (k : ℕ) (t : ℝ) : Measurable (eWk k w t) :=
  (continuous_norm.pow _).measurable.mul (measurable_eW hG t)

include hν hfix hG hRb in
/-- **The weighted energy is differentiable, with the dissipation/trilinear split.** -/
theorem hasDerivAt_EWk (k : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (EWk k w) (∫ ξ, ‖ξ‖ ^ (2 * k) * dW ν w s ξ) s := by
  obtain ⟨Bd, hBd, Bd', hBd', hb, hb'⟩ := weighted_bounds hν hG hRb k
  have hb1 : ∀ᵐ ξ ∂(volume : Measure ES), ‖eWk k w s ξ‖ ≤ Bd ξ := by
    filter_upwards [hb] with ξ h
    rw [Real.norm_eq_abs]; exact h s (Ioo_subset_Icc_self hs)
  have hb2 : ∀ᵐ ξ ∂(volume : Measure ES), ∀ r ∈ Ioo (0 : ℝ) T,
      ‖‖ξ‖ ^ (2 * k) * dW ν w r ξ‖ ≤ Bd' ξ := by
    filter_upwards [hb'] with ξ h r hr
    rw [Real.norm_eq_abs]; exact h r (Ioo_subset_Icc_self hr)
  have hd : ∀ᵐ ξ ∂(volume : Measure ES), ∀ r ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun q => eWk k w q ξ) (‖ξ‖ ^ (2 * k) * dW ν w r ξ) r := by
    filter_upwards [hasDerivAt_eW hν a hfix hG] with ξ h r hr
    exact (h r hr).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ES))
    (F := fun r ξ => eWk k w r ξ) (F' := fun r ξ => ‖ξ‖ ^ (2 * k) * dW ν w r ξ) (x₀ := s)
    (bound := Bd') (Ioo_mem_nhds hs.1 hs.2)
    (Eventually.of_forall fun r => (measurable_eWk hG k r).aestronglyMeasurable)
    (hBd.mono' (measurable_eWk hG k s).aestronglyMeasurable hb1)
    (((continuous_norm.pow _).measurable.mul (measurable_dW hν hG s)).aestronglyMeasurable)
    hb2 hBd' hd
  exact h.2

include hν hG hRb in
theorem continuousOn_EWk (k : ℕ) : ContinuousOn (EWk k w) (Icc (0 : ℝ) T) := by
  obtain ⟨Bd, hBd, -, -, hb, -⟩ := weighted_bounds hν hG hRb k
  have hb1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ᵐ ξ ∂(volume : Measure ES), ‖eWk k w r ξ‖ ≤ Bd ξ := by
    intro r hr
    filter_upwards [hb] with ξ h
    rw [Real.norm_eq_abs]; exact h r hr
  refine continuousOn_of_dominated (bound := Bd)
    (fun r _ => (measurable_eWk hG k r).aestronglyMeasurable) hb1 hBd ?_
  filter_upwards [hG.2.choose_spec.2.2.2] with ξ h
  unfold eWk eW
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp_continuousOn h).norm.pow 2

include hν hG hRb in
/-- **The split of the weighted derivative into dissipation and trilinear term.** -/
theorem integral_weighted_dW (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ ξ, ‖ξ‖ ^ (2 * k) * dW ν w t ξ = -(2 * ν) * EWk (k + 1) w t + 2 * (TWk k w t).re := by
  obtain ⟨-, MB, hMB, hbB, hmomB, -⟩ := good_bil hG hG
  have hMBt : ∀ᵐ ξ ∂(volume : Measure ES), MB ξ < ⊤ :=
    ae_lt_top hMB (lintegral_ne_top_of_mom hmomB)
  have hI1 : Integrable (fun ξ => eWk (k + 1) w t ξ) := by
    obtain ⟨Bd, hBd, -, -, hb, -⟩ := weighted_bounds hν hG hRb (k + 1)
    refine hBd.mono' (measurable_eWk hG _ t).aestronglyMeasurable ?_
    filter_upwards [hb] with ξ h
    rw [Real.norm_eq_abs]; exact h t ht
  have hI2 : Integrable (fun ξ => ((‖ξ‖ ^ (2 * k) : ℝ) : ℂ) * ∑ i : Fin 3,
      continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)) := by
    refine ((integrable_weight_toReal hMB hmomB (2 * k)).const_mul (3 * R)).mono' ?_ ?_
    · refine ((Complex.measurable_ofReal.comp (continuous_norm.pow _).measurable).mul
        (Finset.measurable_sum _ fun i _ =>
        (((continuous_apply i).comp_stronglyMeasurable
          (stronglyMeasurable_bilinear (hG.1 t) (hG.1 t))).measurable).mul
          (Complex.continuous_conj.measurable.comp
            ((continuous_apply i).comp_stronglyMeasurable (hG.1 t)).measurable))).aestronglyMeasurable
    · filter_upwards [hbB, hRb, hMBt] with ξ h1 h2 h3
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hs : ‖∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)‖ ≤
          3 * R * (MB ξ).toReal := by
        refine (norm_sum_le _ _).trans ?_
        have hi : ∀ i : Fin 3, ‖continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)‖ ≤
            R * (MB ξ).toReal := by
          intro i
          rw [norm_mul, Complex.norm_conj]
          calc ‖continuousNavierBilinear (w t) (w t) ξ i‖ * ‖w t ξ i‖ ≤ (MB ξ).toReal * R :=
                mul_le_mul ((norm_le_pi_norm _ i).trans
                  (norm_le_toReal_of_enorm_le h3.ne (h1 t ht)))
                  ((norm_le_pi_norm _ i).trans (h2 t ht)) (norm_nonneg _) ENNReal.toReal_nonneg
            _ = R * (MB ξ).toReal := by ring
        calc ∑ i : Fin 3, ‖continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)‖
            ≤ ∑ _i : Fin 3, R * (MB ξ).toReal := Finset.sum_le_sum fun i _ => hi i
          _ = 3 * R * (MB ξ).toReal := by simp; ring
      calc ‖ξ‖ ^ (2 * k) * ‖∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i *
            conj (w t ξ i)‖ ≤ ‖ξ‖ ^ (2 * k) * (3 * R * (MB ξ).toReal) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 3 * R * (‖ξ‖ ^ (2 * k) * (MB ξ).toReal) := by ring
  have hpt : ∀ ξ, ‖ξ‖ ^ (2 * k) * dW ν w t ξ =
      -(2 * ν) * eWk (k + 1) w t ξ + 2 * (((‖ξ‖ ^ (2 * k) : ℝ) : ℂ) * ∑ i : Fin 3,
        continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)).re := by
    intro ξ
    rw [dW_eq, Complex.re_ofReal_mul]
    unfold eWk
    ring
  have hI2r : Integrable (fun ξ => (((‖ξ‖ ^ (2 * k) : ℝ) : ℂ) * ∑ i : Fin 3,
      continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)).re) := hI2.re
  simp_rw [hpt]
  rw [integral_add (hI1.const_mul _) (hI2r.const_mul 2), integral_const_mul,
    integral_const_mul]
  unfold EWk TWk
  congr 2
  have := integral_re hI2
  simp only [RCLike.re_to_complex] at this
  exact this

end Navier.Analysis.WienerHigherEnergy

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerHigherEnergy.hasDerivAt_EWk
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerHigherEnergy.integral_weighted_dW
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerHigherEnergy.continuousOn_EWk
