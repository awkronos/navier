import Navier.Analysis.WienerLinfBound
import Navier.Analysis.WienerEnergyCancel
import Navier.Analysis.WienerPhysicalAssembly

/-!
# Frequency-side energy decay of the Wiener solution

For a pointwise mild fixed point `w` whose time slices are uniformly essentially
bounded, transversal and reflection-symmetric, the Fourier energy
`E(t) = ∫ ∑ᵢ |wᵢ(t,ξ)|² dξ` is antitone on `[0,T]`:
`E'(t) = -2ν ∫ ‖ξ‖² ∑ᵢ |wᵢ|² + 2 Re ∫ ∑ᵢ conj(wᵢ) Bilᵢ(w,w) ≤ 0`, the second term
vanishing by `WienerEnergyCancel.trilinear_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution ComplexConjugate

namespace Navier.Analysis.WienerEnergy

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerPointwiseBridge
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerLinfBound

variable {ν T : ℝ}

/-- **Pointwise Duhamel bound at every frequency** for a family whose time slices
are essentially bounded by `R` with `L¹` mass at most `3B`. -/
theorem norm_continuousDuhamel_le (hν : 0 < ν) {v : ℝ → ES → ComplexSpace} {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hv : ∀ s ∈ Icc (0 : ℝ) T, (∀ᵐ ζ ∂(volume : Measure ES), ‖v s ζ‖ ≤ R) ∧
      ∫⁻ η, ‖v s η‖ₑ ≤ 3 * ENNReal.ofReal B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (ξ : ES) (i : Fin 3) :
    ‖continuousDuhamel ν v v t ξ i‖ ≤ 27 * R * B * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
  set c : ℝ := 27 * R * B with hc
  have hc0 : 0 ≤ c := by positivity
  set g : ℝ → ℝ := (Ioc 0 t).indicator (fun σ => singWeight ν σ * c) with hg
  have hgint : Integrable g (volume.restrict (Ioc (0 : ℝ) T)) := by
    rw [hg, integrable_indicator_iff measurableSet_Ioc]
    refine ((integrableOn_singWeight ν ht.1).mul_const c).mono_measure ?_
    exact Measure.restrict_mono subset_rfl Measure.restrict_le_self
  have hgval : ∫ σ in Ioc (0 : ℝ) T, g σ = c * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
    rw [hg, setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_self,
      min_eq_right ht.2, integral_mul_const, integral_singWeight ν ht.1]
    ring
  rw [← integral_gDuh_eq ν v ht.1 ht.2 i ξ, ← hgval]
  refine norm_integral_le_of_norm_le hgint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
  by_cases hle : σ ≤ t
  · have hs : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hσ.1, ht.2]⟩
    obtain ⟨hb1, hb2⟩ := hv (t - σ) hs
    have hbil := enorm_bil_le_of_bound (v (t - σ)) hR hb1 hb2 ξ
    have hbil' : ‖continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ‖ ≤ ‖ξ‖ * c := by
      rw [← ofReal_norm] at hbil
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbil
    unfold gDuh
    rw [Set.indicator_of_mem (show σ ∈ Iic t from hle), hg,
      Set.indicator_of_mem (show σ ∈ Ioc 0 t from ⟨hσ.1, hle⟩), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
    calc heatFactor ν σ ξ * ‖continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ i‖
        ≤ heatFactor ν σ ξ * (‖ξ‖ * c) :=
          mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ i).trans hbil')
            (heatFactor_nonneg _ _ _)
      _ = (heatFactor ν σ ξ * ‖ξ‖) * c := by ring
      _ ≤ singWeight ν σ * c := mul_le_mul_of_nonneg_right (heat_mul_norm_le hν hσ.1 ξ) hc0
  · unfold gDuh
    rw [Set.indicator_of_notMem (show σ ∉ Iic t from hle), norm_zero, hg,
      Set.indicator_of_notMem (show σ ∉ Ioc 0 t from fun h => hle h.2)]

/-- Slice properties of a family represented by an essentially bounded path. -/
theorem slice_props (hT : 0 < T) {w : ℝ → ES → ComplexSpace} (x : C(Icc (0 : ℝ) T, V1))
    (hwm : ∀ t, StronglyMeasurable (w t))
    (hxw : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i))
    {R B : ℝ} (hR : 0 ≤ R) (hxS : x ∈ linfSet T R) (hxB : ‖x‖ ≤ B) :
    ∀ s ∈ Icc (0 : ℝ) T, (∀ᵐ ζ ∂(volume : Measure ES), ‖w s ζ‖ ≤ R) ∧
      ∫⁻ η, ‖w s η‖ₑ ≤ 3 * ENNReal.ofReal B := by
  intro s hs
  refine ⟨?_, ?_⟩
  · have hc : ∀ᵐ ζ ∂(volume : Measure ES), ∀ j : Fin 3, ‖w s ζ j‖ ≤ R := by
      refine ae_all_iff.mpr fun j => ?_
      filter_upwards [hxw s hs j, hxS ⟨s, hs⟩ j] with ζ h1 h2
      rw [h1]; exact h2
    filter_upwards [hc] with ζ h
    exact (pi_norm_le_iff_of_nonneg hR).mpr h
  · calc ∫⁻ η, ‖w s η‖ₑ ≤ ∫⁻ η, ∑ j : Fin 3, ‖w s η j‖ₑ :=
          lintegral_mono fun η => WienerMildGood.enorm_le_sum_coord _
      _ = ∑ j : Fin 3, ∫⁻ η, ‖w s η j‖ₑ := by
          refine lintegral_finsetSum _ fun j _ => ?_
          exact (show Measurable (fun η => w s η j) from
            ((continuous_apply j).comp_stronglyMeasurable (hwm s)).measurable).enorm
      _ ≤ ∑ _j : Fin 3, ENNReal.ofReal B := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [lintegral_congr_ae (by filter_upwards [hxw s hs j] with η h; rw [h]),
            ← L1.ofReal_norm_eq_lintegral]
          exact ENNReal.ofReal_le_ofReal ((norm_le_pi_norm _ j).trans
            ((x.norm_coe_le_norm _).trans hxB))
      _ = 3 * ENNReal.ofReal B := by simp

/-- **Uniform-in-time essential bound** for the mild fixed point. -/
theorem ae_uniform_bound (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
    {w : ℝ → ES → ComplexSpace}
    (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
    (x : C(Icc (0 : ℝ) T, V1)) (hwm : ∀ t, StronglyMeasurable (w t))
    (hxw : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hxS : x ∈ linfSet T (2 * A)) (hxB : ‖x‖ ≤ B)
    (hab : ∀ᵐ ξ ∂(volume : Measure ES), ∀ i, ‖a ξ i‖ ≤ A) :
    ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T,
      ‖w t ξ‖ ≤ A + 27 * (2 * A) * B * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt T) := by
  have hsl := slice_props hT x hwm hxw (by positivity) hxS hxB
  filter_upwards [hab] with ξ hξ t ht
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [hfix t ht ξ]
  show ‖heatVec ν t a ξ i + continuousDuhamel ν w w t ξ i‖ ≤ _
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [WienerMildGood.heatVec_eq_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hξ i)
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by have := ht.1; positivity
    linarith
  · refine (norm_continuousDuhamel_le hν (by positivity) hB hsl ht ξ i).trans ?_
    have : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
    gcongr

/-! ## The energy of a transversal, reflection-symmetric, bounded mild solution -/

section Energy

open Navier.Analysis.WienerPhysicalPDE

variable (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace) {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w) {R : ℝ} (hR0 : 0 ≤ R)
  (hRb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖w t ξ‖ ≤ R)
  (hsym : ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3,
    ∀ᵐ ξ ∂(volume : Measure ES), w t (-ξ) i = conj (w t ξ i))
  (ha : Navier.Analysis.ContinuousLeiLinReality.ProfileDivergenceFree a)

include hG in
theorem integrable_pow_norm_w {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (n : ℕ) :
    Integrable (fun ξ => ‖ξ‖ ^ n * ‖w t ξ‖) := by
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hG
  refine ⟨((continuous_norm.pow n).aestronglyMeasurable).mul (hm t).norm.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hmom n).lt_top
  filter_upwards [hb] with ξ h
  rw [enorm_mul, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ofReal_norm]
  exact mul_le_mul' le_rfl (h t ht)

include hT hν hfix hG hR0 hRb hsym ha in
/-- **The energy cancellation at a fixed time.** -/
theorem integral_bil_conj_eq_zero {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ∫ ξ, ∑ i : Fin 3, continuousNavierBilinear (w s) (w s) ξ i * conj (w s ξ i) = 0 := by
  set u : ES → ComplexSpace := w s with hu
  have hum : StronglyMeasurable u := hG.1 s
  set ut : ES → ComplexSpace := fun ξ => if ‖u ξ‖ ≤ R then u ξ else 0 with hut
  have hutm : StronglyMeasurable ut :=
    (hum.measurable.ite (measurableSet_le hum.measurable.norm measurable_const)
      measurable_const).stronglyMeasurable
  have hRs : ∀ᵐ ξ ∂(volume : Measure ES), ‖u ξ‖ ≤ R := by
    filter_upwards [hRb] with ξ h using h s hs
  have hut_eq : ∀ᵐ ξ ∂(volume : Measure ES), ut ξ = u ξ := by
    filter_upwards [hRs] with ξ h
    simp [hut, h]
  have hutb : ∀ ξ, ‖ut ξ‖ ≤ R := fun ξ => by
    by_cases h : ‖u ξ‖ ≤ R
    · simp [hut, h]
    · simp [hut, h, hR0]
  have hutle : ∀ ξ, ‖ut ξ‖ ≤ ‖u ξ‖ := fun ξ => by
    by_cases h : ‖u ξ‖ ≤ R
    · simp [hut, h]
    · simp [hut, h]
  have hi0 : Integrable (fun ξ => ‖ut ξ‖) := by
    refine (show Integrable (fun ξ => ‖u ξ‖) by
      simpa using integrable_pow_norm_w hG hs 0).mono' hutm.norm.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_norm]; exact hutle ξ
  have hi1 : Integrable (fun ξ => ‖ξ‖ * ‖ut ξ‖) := by
    refine (show Integrable (fun ξ => ‖ξ‖ * ‖u ξ‖) by
      simpa using integrable_pow_norm_w hG hs 1).mono'
      ((continuous_norm.aestronglyMeasurable).mul hutm.norm.aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    show ‖‖ξ‖ * ‖ut ξ‖‖ ≤ ‖ξ‖ * ‖u ξ‖
    rw [norm_mul, norm_norm, norm_norm]
    exact mul_le_mul_of_nonneg_left (hutle ξ) (norm_nonneg _)
  have htr_u := Navier.Analysis.WienerPhysicalAssembly.transverse_mild hν a hfix hG ha hs
  have htr : ∀ᵐ η ∂(volume : Measure ES), ∑ j : Fin 3, ((η j : ℝ) : ℂ) * ut η j = 0 := by
    filter_upwards [htr_u, hut_eq] with η h1 h2
    rw [h2]; exact h1
  have hzero := Navier.Analysis.WienerEnergyCancel.trilinear_zero hutm hutb hi0 hi1 htr
  have hconv : ∀ j i : Fin 3,
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => u η i)) =
      ((fun η => ut η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => ut η i)) := by
    intro j i
    refine convolution_congr (ContinuousLinearMap.mul ℂ ℂ) ?_ ?_
    · filter_upwards [hut_eq] with η h; rw [h]
    · filter_upwards [hut_eq] with η h; rw [h]
  have hsymi : ∀ᵐ ξ ∂(volume : Measure ES), ∀ i, conj (u ξ i) = ut (-ξ) i := by
    refine ae_all_iff.mpr fun i => ?_
    filter_upwards [hsym s hs i, Navier.Analysis.WienerReality.ae_neg hut_eq] with ξ h1 h2
    rw [h2, hu, h1]
  have hpt : ∀ᵐ ξ ∂(volume : Measure ES),
      ∑ i : Fin 3, continuousNavierBilinear (w s) (w s) ξ i * conj (w s ξ i) =
      Complex.I * ∑ i : Fin 3, ut (-ξ) i * ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
        ((fun η => ut η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => ut η i)) ξ := by
    filter_upwards [hsymi, htr_u] with ξ h1 h2
    have hc : ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * conj (w s ξ i) = 0 := by
      have := congrArg conj h2
      simp only [map_sum, map_mul, Complex.conj_ofReal, map_zero] at this
      exact this
    simp_rw [bil_formula (w := w) s ξ]
    have hsplit : ∑ i : Fin 3, (∑ j : Fin 3, Complex.I * (((ξ j : ℝ) : ℂ) * cc w s j i ξ) +
        (-Complex.I) * (((ξ i : ℝ) : ℂ) * Qhat w s ξ)) * conj (w s ξ i) =
        ∑ i : Fin 3, (∑ j : Fin 3, Complex.I * (((ξ j : ℝ) : ℂ) * cc w s j i ξ)) *
          conj (w s ξ i) +
        (-Complex.I) * Qhat w s ξ * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * conj (w s ξ i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsplit, hc, mul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hu, h1 i, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold cc
    rw [← hu, hconv j i]
    ring
  rw [integral_congr_ae hpt, integral_const_mul, hzero, mul_zero]

/-- The pointwise energy density `∑ᵢ |wᵢ|²`. -/
def eW (w : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ℝ := ∑ i : Fin 3, ‖w t ξ i‖ ^ 2

/-- The Fourier energy. -/
def EW (w : ℝ → ES → ComplexSpace) (t : ℝ) : ℝ := ∫ ξ, eW w t ξ

/-- Its time-derivative density. -/
def dW (ν : ℝ) (w : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ℝ :=
  ∑ i : Fin 3, 2 * (W ν w 1 t ξ i * conj (w t ξ i)).re

/-- A majorant turned real. -/
theorem integrable_toReal_majorant {M : ES → ℝ≥0∞} (hM : Measurable M)
    (hmom : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * M ξ ≠ ⊤) :
    Integrable (fun ξ => (M ξ).toReal) :=
  integrable_toReal_of_lintegral_ne_top hM.aemeasurable (lintegral_ne_top_of_mom hmom)

theorem norm_le_toReal_of_enorm_le {z : ComplexSpace} {m : ℝ≥0∞} (hm : m ≠ ⊤)
    (h : ‖z‖ₑ ≤ m) : ‖z‖ ≤ m.toReal := by
  rw [← ENNReal.toReal_ofReal (norm_nonneg z), ofReal_norm]
  exact ENNReal.toReal_mono hm h

theorem eW_le {z : ES → ComplexSpace} {R : ℝ} {ξ : ES} (h : ‖z ξ‖ ≤ R) :
    ∑ i : Fin 3, ‖z ξ i‖ ^ 2 ≤ 3 * R * ‖z ξ‖ := by
  have hi : ∀ i, ‖z ξ i‖ ^ 2 ≤ R * ‖z ξ‖ := fun i => by
    rw [sq]
    exact mul_le_mul ((norm_le_pi_norm _ i).trans h) (norm_le_pi_norm _ i) (norm_nonneg _)
      ((norm_nonneg _).trans h)
  calc ∑ i : Fin 3, ‖z ξ i‖ ^ 2 ≤ ∑ _i : Fin 3, R * ‖z ξ‖ := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * R * ‖z ξ‖ := by simp; ring

include hν hG hRb in
theorem energy_bounds :
    ∃ Bd : ES → ℝ, Integrable Bd ∧ ∃ Bd' : ES → ℝ, Integrable Bd' ∧
      (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, |eW w t ξ| ≤ Bd ξ) ∧
      (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, |dW ν w t ξ| ≤ Bd' ξ) := by
  obtain ⟨-, M1, hM1, hb1, hmom1, -⟩ := good_W hν.le hG 1
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hG
  have hMt : ∀ᵐ ξ ∂(volume : Measure ES), M ξ < ⊤ :=
    ae_lt_top hM (lintegral_ne_top_of_mom hmom)
  have hM1t : ∀ᵐ ξ ∂(volume : Measure ES), M1 ξ < ⊤ :=
    ae_lt_top hM1 (lintegral_ne_top_of_mom hmom1)
  refine ⟨fun ξ => 3 * R * (M ξ).toReal, (integrable_toReal_majorant hM hmom).const_mul _,
    fun ξ => 6 * R * (M1 ξ).toReal, (integrable_toReal_majorant hM1 hmom1).const_mul _, ?_, ?_⟩
  · filter_upwards [hb, hRb, hMt] with ξ h1 h2 h3 t ht
    have hR : 0 ≤ R := (norm_nonneg _).trans (h2 t ht)
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
    refine (eW_le (h2 t ht)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_le_toReal_of_enorm_le h3.ne (h1 t ht)) (by positivity)
  · filter_upwards [hb1, hRb, hM1t] with ξ h1 h2 h3 t ht
    have hR : 0 ≤ R := (norm_nonneg _).trans (h2 t ht)
    unfold dW
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hi : ∀ i : Fin 3, |2 * (W ν w 1 t ξ i * conj (w t ξ i)).re| ≤ 2 * R * (M1 ξ).toReal := by
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

include hG in
theorem measurable_eW (t : ℝ) : Measurable (eW w t) := by
  unfold eW
  exact Finset.measurable_sum _ fun i _ =>
    (((continuous_apply i).comp_stronglyMeasurable (hG.1 t)).measurable.norm).pow_const 2

include hν hG in
theorem measurable_dW (t : ℝ) : Measurable (dW ν w t) := by
  unfold dW
  have h1 := (good_W hν.le hG 1).1 t
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul
    (Complex.measurable_re.comp
      ((((continuous_apply i).comp_stronglyMeasurable h1).measurable).mul
        (Complex.continuous_conj.measurable.comp
          ((continuous_apply i).comp_stronglyMeasurable (hG.1 t)).measurable)))

include hν hfix hG in
theorem hasDerivAt_eW : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Ioo (0 : ℝ) T,
    HasDerivAt (fun s => eW w s ξ) (dW ν w t ξ) t := by
  filter_upwards [hasTimeDeriv_W_zero hν a hfix hG] with ξ h t ht
  have hc : ∀ i : Fin 3, HasDerivAt (fun s => w s ξ i) (W ν w 1 t ξ i) t := fun i =>
    (hasDerivAt_pi.mp (h t ht)) i
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).norm_sq
  unfold eW dW
  refine hs.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  rw [Complex.inner]

/-- The pointwise split of the derivative density. -/
theorem dW_eq (t : ℝ) (ξ : ES) :
    dW ν w t ξ = -(2 * ν) * (‖ξ‖ ^ 2 * eW w t ξ) +
      2 * (∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)).re := by
  unfold dW eW
  simp_rw [WienerPhysicalPDE.W_one, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib,
    Complex.re_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold heatSym2
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

include hT hν hfix hG hR0 hRb hsym ha in
theorem integral_dW_nonpos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ∫ ξ, dW ν w t ξ ≤ 0 := by
  obtain ⟨-, MB, hMB, hbB, hmomB, -⟩ := good_bil hG hG
  have hMBt : ∀ᵐ ξ ∂(volume : Measure ES), MB ξ < ⊤ :=
    ae_lt_top hMB (lintegral_ne_top_of_mom hmomB)
  have hI1 : Integrable (fun ξ => ‖ξ‖ ^ 2 * eW w t ξ) := by
    refine ((integrable_pow_norm_w hG ht 2).const_mul (3 * R)).mono'
      (((continuous_norm.pow 2).measurable.mul (measurable_eW hG t)).aestronglyMeasurable) ?_
    filter_upwards [hRb] with ξ h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => by positivity))]
    calc ‖ξ‖ ^ 2 * eW w t ξ ≤ ‖ξ‖ ^ 2 * (3 * R * ‖w t ξ‖) :=
          mul_le_mul_of_nonneg_left (eW_le (h t ht)) (by positivity)
      _ = 3 * R * (‖ξ‖ ^ 2 * ‖w t ξ‖) := by ring
  have hI2 : Integrable (fun ξ => ∑ i : Fin 3,
      continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)) := by
    refine ((integrable_toReal_majorant hMB hmomB).const_mul (3 * R)).mono' ?_ ?_
    · refine (Finset.measurable_sum _ fun i _ =>
        (((continuous_apply i).comp_stronglyMeasurable
          (stronglyMeasurable_bilinear (hG.1 t) (hG.1 t))).measurable).mul
          (Complex.continuous_conj.measurable.comp
            ((continuous_apply i).comp_stronglyMeasurable (hG.1 t)).measurable)).aestronglyMeasurable
    · filter_upwards [hbB, hRb, hMBt] with ξ h1 h2 h3
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
  have hI2re : Integrable (fun ξ =>
      (∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)).re) := hI2.re
  simp_rw [dW_eq]
  rw [integral_add (hI1.const_mul _) (hI2re.const_mul 2), integral_const_mul,
    integral_const_mul]
  have hre : ∫ ξ, (∑ i : Fin 3, continuousNavierBilinear (w t) (w t) ξ i * conj (w t ξ i)).re
      = 0 := by
    have := integral_re hI2
    simp only [RCLike.re_to_complex] at this
    rw [this, integral_bil_conj_eq_zero hT hν a hfix hG hR0 hRb hsym ha ht, Complex.zero_re]
  rw [hre, mul_zero, add_zero]
  have : 0 ≤ ∫ ξ, ‖ξ‖ ^ 2 * eW w t ξ :=
    integral_nonneg fun ξ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => by positivity)
  nlinarith

include hT hν hfix hG hR0 hRb hsym ha in
/-- **Fourier energy decay** on `[0,T]`. -/
theorem energy_antitone {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : EW w t ≤ EW w 0 := by
  obtain ⟨Bd, hBd, Bd', hBd', hb, hb'⟩ := energy_bounds hν hG hRb
  have hb1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ᵐ ξ ∂(volume : Measure ES), ‖eW w r ξ‖ ≤ Bd ξ := by
    intro r hr
    filter_upwards [hb] with ξ h
    rw [Real.norm_eq_abs]; exact h r hr
  have hb2 : ∀ᵐ ξ ∂(volume : Measure ES), ∀ r ∈ Ioo (0 : ℝ) T, ‖dW ν w r ξ‖ ≤ Bd' ξ := by
    filter_upwards [hb'] with ξ h r hr
    rw [Real.norm_eq_abs]; exact h r (Ioo_subset_Icc_self hr)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (EW w) (∫ ξ, dW ν w s ξ) s := by
    intro s hs
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ES))
      (F := fun r ξ => eW w r ξ) (F' := fun r ξ => dW ν w r ξ) (x₀ := s) (bound := Bd')
      (Ioo_mem_nhds hs.1 hs.2)
      (Eventually.of_forall fun r => (measurable_eW hG r).aestronglyMeasurable)
      (hBd.mono' (measurable_eW hG s).aestronglyMeasurable (hb1 s (Ioo_subset_Icc_self hs)))
      (measurable_dW hν hG s).aestronglyMeasurable hb2 hBd' (hasDerivAt_eW hν a hfix hG)
    exact h.2
  have hcont : ContinuousOn (EW w) (Icc (0 : ℝ) T) := by
    refine continuousOn_of_dominated (bound := Bd)
      (fun r _ => (measurable_eW hG r).aestronglyMeasurable) hb1 hBd ?_
    filter_upwards [hG.2.choose_spec.2.2.2] with ξ h
    unfold eW
    refine continuousOn_finset_sum _ fun i _ => ?_
    have hci : ContinuousOn (fun x => w x ξ i) (Icc (0 : ℝ) T) :=
      (continuous_apply i).comp_continuousOn h
    exact hci.norm.pow 2
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont
    (fun s hs => by
      rw [interior_Icc] at hs
      exact (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hderiv s hs).deriv]
      exact integral_dW_nonpos hT hν a hfix hG hR0 hRb hsym ha (Ioo_subset_Icc_self hs))
  exact hanti ⟨le_rfl, hT.le⟩ ht ht.1

end Energy

end Navier.Analysis.WienerEnergy

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerEnergy.energy_antitone
