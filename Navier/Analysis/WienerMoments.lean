import Navier.Analysis.WienerLocalMild
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Fourier moments on the Wiener carrier

`mom n f = ∫ ‖ξ‖ⁿ ‖f(ξ)‖ dξ ∈ [0, ∞]` for `f ∈ L¹(ℝ³; ℂ)`.  This module proves
the estimates that propagate moments through the Duhamel map:

* `lowerSemicontinuous_mom`: `mom n` is lower semicontinuous on `L¹`, so its
  sublevel sets are closed;
* `mom_integral_le`: Minkowski's inequality for `L¹`-valued Bochner integrals;
* `mom_mulL_le`: bounded multipliers act with their sup bound;
* `mom_conv_le`: `mom n (f ⋆ g) ≤ 2ⁿ (mom n f · ‖g‖ + ‖f‖ · mom n g)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution

namespace Navier.Analysis.WienerMoments

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild

/-- The `n`-th Fourier moment of an `L¹` class. -/
def mom (n : ℕ) (f : L1C) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ‖ₑ

theorem mom_zero (f : L1C) : mom 0 f = ENNReal.ofReal ‖f‖ := by
  rw [L1.ofReal_norm_eq_lintegral]
  simp [mom]

/-! ## Truncations and lower semicontinuity -/

/-- Truncated weight `min(‖ξ‖ⁿ, N)`. -/
def truncW (n N : ℕ) (ξ : ES) : ℝ := min (‖ξ‖ ^ n) (N : ℝ)

theorem truncW_nonneg (n N : ℕ) (ξ : ES) : 0 ≤ truncW n N ξ :=
  le_min (by positivity) (Nat.cast_nonneg N)

theorem measurable_truncW (n N : ℕ) : Measurable (truncW n N) :=
  ((continuous_norm.pow n).min continuous_const).measurable

/-- The truncated weight as a bounded multiplier. -/
def truncLinf (n N : ℕ) : LinfC :=
  linfOfBound (fun ξ => ((truncW n N ξ : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp (measurable_truncW n N)).aestronglyMeasurable N
    (fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (truncW_nonneg n N ξ)]
      exact min_le_right _ _)

theorem enorm_ofReal_complex {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem ofReal_norm_mulL_trunc (n N : ℕ) (f : L1C) :
    ENNReal.ofReal ‖mulL (truncLinf n N) f‖ =
      ∫⁻ ξ, ENNReal.ofReal (truncW n N ξ) * ‖f ξ‖ₑ := by
  rw [L1.ofReal_norm_eq_lintegral]
  apply lintegral_congr_ae
  filter_upwards [coeFn_mulL (truncLinf n N) f, coeFn_linfOfBound _ _ _ _] with ξ h1 h2
  rw [h1, enorm_mul]
  unfold truncLinf
  rw [h2, enorm_ofReal_complex (truncW_nonneg n N ξ)]

theorem iSup_ofReal_min (a : ℝ) :
    ⨆ N : ℕ, ENNReal.ofReal (min a (N : ℝ)) = ENNReal.ofReal a := by
  apply le_antisymm
  · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · obtain ⟨N, hN⟩ := exists_nat_ge a
    exact le_iSup_of_le N (by rw [min_eq_left hN])

theorem mom_eq_iSup (n : ℕ) (f : L1C) :
    mom n f = ⨆ N : ℕ, ENNReal.ofReal ‖mulL (truncLinf n N) f‖ := by
  simp_rw [ofReal_norm_mulL_trunc]
  unfold mom
  have hfm : Measurable fun ξ => ‖f ξ‖ₑ := (Lp.stronglyMeasurable f).enorm
  have hmeas : ∀ N : ℕ, Measurable (fun ξ => ENNReal.ofReal (truncW n N ξ) * ‖f ξ‖ₑ) :=
    fun N => (ENNReal.measurable_ofReal.comp (measurable_truncW n N)).mul hfm
  have hmono : Monotone (fun N : ℕ => fun ξ => ENNReal.ofReal (truncW n N ξ) * ‖f ξ‖ₑ) := by
    intro N M hNM ξ
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact min_le_min_left _ (by exact_mod_cast hNM)
  rw [← lintegral_iSup hmeas hmono]
  congr 1
  funext ξ
  rw [← ENNReal.iSup_mul]
  congr 1
  exact (iSup_ofReal_min _).symm

theorem lowerSemicontinuous_mom (n : ℕ) : LowerSemicontinuous (mom n) := by
  have h : mom n = fun f => ⨆ N : ℕ, ENNReal.ofReal ‖mulL (truncLinf n N) f‖ :=
    funext (mom_eq_iSup n)
  rw [h]
  exact lowerSemicontinuous_iSup fun N =>
    (ENNReal.continuous_ofReal.comp (continuous_norm.comp (mulL _).continuous)).lowerSemicontinuous

/-- Precomposition of a lower semicontinuous function with a continuous map. -/
theorem lsc_comp_continuous {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : β → ℝ≥0∞} (hf : LowerSemicontinuous f) {g : α → β} (hg : Continuous g) :
    LowerSemicontinuous (f ∘ g) :=
  fun x y hy => (hg.tendsto x).eventually (hf (g x) y hy)

/-! ## Minkowski's inequality for Bochner integrals -/

theorem mom_integral_le (n : ℕ) {S : Set ℝ} (G : ℝ → L1C) (hG : Integrable G (volume.restrict S))
    (b : ℝ → ℝ) (hb : Integrable b (volume.restrict S)) (hb0 : ∀ σ, 0 ≤ b σ)
    (hGb : ∀ᵐ σ ∂(volume.restrict S), mom n (G σ) ≤ ENNReal.ofReal (b σ)) :
    mom n (∫ σ in S, G σ) ≤ ENNReal.ofReal (∫ σ in S, b σ) := by
  rw [mom_eq_iSup]
  refine iSup_le fun N => ?_
  rw [← (mulL (truncLinf n N)).integral_comp_comm hG]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_ae ((mulL (truncLinf n N)).integrable_comp hG).norm hb ?_)
  filter_upwards [hGb] with σ h
  have h1 : ENNReal.ofReal ‖mulL (truncLinf n N) (G σ)‖ ≤ ENNReal.ofReal (b σ) :=
    (le_iSup (fun M : ℕ => ENNReal.ofReal ‖mulL (truncLinf n M) (G σ)‖) N).trans
      ((mom_eq_iSup n (G σ)).symm.le.trans h)
  exact (ENNReal.ofReal_le_ofReal_iff (hb0 σ)).mp h1

/-! ## Multipliers and sums -/

theorem mom_mulL_le (n : ℕ) (m : LinfC) {c : ℝ}
    (hm : ∀ᵐ ξ ∂(volume : Measure ES), ‖m ξ‖ ≤ c) (f : L1C) :
    mom n (mulL m f) ≤ ENNReal.ofReal c * mom n f := by
  unfold mom
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [coeFn_mulL m f, hm] with ξ h1 h2
  rw [h1, enorm_mul]
  have h3 : ‖m ξ‖ₑ ≤ ENNReal.ofReal c := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h2
  calc ENNReal.ofReal (‖ξ‖ ^ n) * (‖m ξ‖ₑ * ‖f ξ‖ₑ)
      ≤ ENNReal.ofReal (‖ξ‖ ^ n) * (ENNReal.ofReal c * ‖f ξ‖ₑ) := by gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ‖ₑ) := by ring

theorem mom_add_le (n : ℕ) (f g : L1C) : mom n (f + g) ≤ mom n f + mom n g := by
  unfold mom
  have hm : Measurable (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ‖f ξ‖ₑ) :=
    (ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul
      (Lp.stronglyMeasurable f).enorm
  rw [← lintegral_add_left hm]
  apply lintegral_mono_ae
  filter_upwards [Lp.coeFn_add f g] with ξ h
  rw [h, Pi.add_apply, ← mul_add]
  gcongr
  exact enorm_add_le _ _

theorem mom_sum_le (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → L1C) :
    mom n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mom n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold mom
      rw [nonpos_iff_eq_zero, lintegral_eq_zero_iff' (by
        exact ((ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul
          (Lp.stronglyMeasurable (0 : L1C)).enorm).aemeasurable)]
      filter_upwards [Lp.coeFn_zero ℂ 1 (volume : Measure ES)] with ξ h
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (mom_add_le n _ _).trans (add_le_add le_rfl ih)

/-! ## The convolution moment estimate -/

theorem pow_norm_le_two_pow (n : ℕ) (ξ η : ES) :
    ‖ξ‖ ^ n ≤ 2 ^ n * (‖η‖ ^ n + ‖ξ - η‖ ^ n) := by
  have h : ‖ξ‖ ≤ 2 * max ‖η‖ ‖ξ - η‖ := by
    have := norm_add_le η (ξ - η)
    rw [add_sub_cancel] at this
    linarith [le_max_left ‖η‖ ‖ξ - η‖, le_max_right ‖η‖ ‖ξ - η‖]
  have hmax : max ‖η‖ ‖ξ - η‖ ^ n ≤ ‖η‖ ^ n + ‖ξ - η‖ ^ n := by
    rcases le_total ‖η‖ ‖ξ - η‖ with hle | hle
    · rw [max_eq_right hle]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left hle]; exact le_add_of_nonneg_right (by positivity)
  calc ‖ξ‖ ^ n ≤ (2 * max ‖η‖ ‖ξ - η‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) h n
    _ = 2 ^ n * max ‖η‖ ‖ξ - η‖ ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (‖η‖ ^ n + ‖ξ - η‖ ^ n) := by gcongr

theorem ofReal_pow_norm_le (n : ℕ) (ξ η : ES) :
    ENNReal.ofReal (‖ξ‖ ^ n) ≤
      2 ^ n * ENNReal.ofReal (‖η‖ ^ n) + 2 ^ n * ENNReal.ofReal (‖ξ - η‖ ^ n) := by
  calc ENNReal.ofReal (‖ξ‖ ^ n) ≤ ENNReal.ofReal (2 ^ n * (‖η‖ ^ n + ‖ξ - η‖ ^ n)) :=
        ENNReal.ofReal_le_ofReal (pow_norm_le_two_pow n ξ η)
    _ = 2 ^ n * ENNReal.ofReal (‖η‖ ^ n) + 2 ^ n * ENNReal.ofReal (‖ξ - η‖ ^ n) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_add]

theorem enorm_convolution_le (F G : ES → ℂ) (ξ : ES) :
    ‖(F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) ξ‖ₑ ≤ ∫⁻ η, ‖F η‖ₑ * ‖G (ξ - η)‖ₑ := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext η
  rw [ContinuousLinearMap.mul_apply', enorm_mul]

theorem mom_zero_eq_lintegral (f : L1C) : mom 0 f = ∫⁻ ξ, ‖f ξ‖ₑ := by
  simp [mom]

theorem lintegral_weight_conv_le (n : ℕ) (F G : ES → ℂ)
    (hF : Measurable fun η => ‖F η‖ₑ) (hG : Measurable fun η => ‖G η‖ₑ) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖(F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) ξ‖ₑ ≤
      2 ^ n * ((∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * ‖F η‖ₑ) * (∫⁻ η, ‖G η‖ₑ)) +
      2 ^ n * ((∫⁻ η, ‖F η‖ₑ) * ∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * ‖G η‖ₑ) := by
  have hw : Measurable fun η : ES => ENNReal.ofReal (‖η‖ ^ n) :=
    ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable
  have hsub : Measurable fun p : ES × ES => p.1 - p.2 := measurable_fst.sub measurable_snd
  let A : ES → ES → ℝ≥0∞ := fun ξ η =>
    (2 ^ n * (ENNReal.ofReal (‖η‖ ^ n) * ‖F η‖ₑ)) * ‖G (ξ - η)‖ₑ
  let B : ES → ES → ℝ≥0∞ := fun ξ η =>
    (2 ^ n * ‖F η‖ₑ) * (ENNReal.ofReal (‖ξ - η‖ ^ n) * ‖G (ξ - η)‖ₑ)
  have hAm : Measurable (Function.uncurry A) :=
    (measurable_const.mul ((hw.comp measurable_snd).mul (hF.comp measurable_snd))).mul
      (hG.comp hsub)
  have hBm : Measurable (Function.uncurry B) :=
    (measurable_const.mul (hF.comp measurable_snd)).mul ((hw.comp hsub).mul (hG.comp hsub))
  have hpt : ∀ ξ, ENNReal.ofReal (‖ξ‖ ^ n) *
      ‖(F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) ξ‖ₑ ≤ (∫⁻ η, A ξ η) + ∫⁻ η, B ξ η := by
    intro ξ
    have hAξ : Measurable (A ξ) := hAm.of_uncurry_left
    rw [← lintegral_add_left hAξ]
    calc ENNReal.ofReal (‖ξ‖ ^ n) * ‖(F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) ξ‖ₑ
        ≤ ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, ‖F η‖ₑ * ‖G (ξ - η)‖ₑ := by
          gcongr; exact enorm_convolution_le F G ξ
      _ = ∫⁻ η, ENNReal.ofReal (‖ξ‖ ^ n) * (‖F η‖ₑ * ‖G (ξ - η)‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (A ξ η + B ξ η) := by
          refine lintegral_mono fun η => ?_
          calc ENNReal.ofReal (‖ξ‖ ^ n) * (‖F η‖ₑ * ‖G (ξ - η)‖ₑ)
              ≤ (2 ^ n * ENNReal.ofReal (‖η‖ ^ n) + 2 ^ n * ENNReal.ofReal (‖ξ - η‖ ^ n)) *
                  (‖F η‖ₑ * ‖G (ξ - η)‖ₑ) := by
                gcongr; exact ofReal_pow_norm_le n ξ η
            _ = A ξ η + B ξ η := by simp only [A, B]; ring
  have hT1 : ∫⁻ ξ, ∫⁻ η, A ξ η =
      2 ^ n * ((∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * ‖F η‖ₑ) * (∫⁻ η, ‖G η‖ₑ)) := by
    rw [lintegral_lintegral_swap hAm.aemeasurable]
    have hin : ∀ η, ∫⁻ ξ, A ξ η =
        (2 ^ n * (ENNReal.ofReal (‖η‖ ^ n) * ‖F η‖ₑ)) * ∫⁻ ξ, ‖G ξ‖ₑ := by
      intro η
      simp only [A]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top))]
      congr 1
      exact lintegral_sub_right_eq_self (fun ξ => ‖G ξ‖ₑ) η
    simp_rw [hin]
    have hc : Measurable fun y : ES => 2 ^ n * (ENNReal.ofReal (‖y‖ ^ n) * ‖F y‖ₑ) :=
      measurable_const.mul (hw.mul hF)
    have hc' : Measurable fun y : ES => ENNReal.ofReal (‖y‖ ^ n) * ‖F y‖ₑ := hw.mul hF
    rw [lintegral_mul_const _ hc, lintegral_const_mul _ hc', mul_assoc]
  have hT2 : ∫⁻ ξ, ∫⁻ η, B ξ η =
      2 ^ n * ((∫⁻ η, ‖F η‖ₑ) * ∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * ‖G η‖ₑ) := by
    rw [lintegral_lintegral_swap hBm.aemeasurable]
    have hin : ∀ η, ∫⁻ ξ, B ξ η =
        (2 ^ n * ‖F η‖ₑ) * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖G ξ‖ₑ := by
      intro η
      simp only [B]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
        enorm_ne_top)]
      congr 1
      exact lintegral_sub_right_eq_self (fun ξ => ENNReal.ofReal (‖ξ‖ ^ n) * ‖G ξ‖ₑ) η
    simp_rw [hin]
    have hc : Measurable fun y : ES => 2 ^ n * ‖F y‖ₑ := measurable_const.mul hF
    rw [lintegral_mul_const _ hc, lintegral_const_mul _ hF, mul_assoc]
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖(F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) ξ‖ₑ
      ≤ ∫⁻ ξ, ((∫⁻ η, A ξ η) + ∫⁻ η, B ξ η) := lintegral_mono hpt
    _ = (∫⁻ ξ, ∫⁻ η, A ξ η) + ∫⁻ ξ, ∫⁻ η, B ξ η :=
        lintegral_add_left (hAm.lintegral_prod_right') _
    _ = _ := by rw [hT1, hT2]

theorem mom_conv_le (n : ℕ) (f g : L1C) :
    mom n (conv f g) ≤ 2 ^ n * (mom n f * mom 0 g) + 2 ^ n * (mom 0 f * mom n g) := by
  have h1 : mom n (conv f g) = ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) *
      ‖((⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g)) ξ‖ₑ := by
    unfold mom
    apply lintegral_congr_ae
    filter_upwards [coeFn_convFun f g] with ξ h
    rw [conv_apply, h]
  rw [h1, mom_zero_eq_lintegral, mom_zero_eq_lintegral]
  exact lintegral_weight_conv_le n _ _ (Lp.stronglyMeasurable f).enorm
    (Lp.stronglyMeasurable g).enorm

/-! ## Picard iteration inside a closed invariant set, and uniqueness -/

/-- Picard's theorem for `x = y + B(x,x)` inside a closed set `S` invariant under
the map on the ball of radius `2‖y‖`. -/
theorem picard_small_data_on {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {B : X → X → X} {C : ℝ} (hC : 0 < C)
    (hB : ∀ a b : X, ‖B a b‖ ≤ C * (‖a‖ * ‖b‖))
    (hdiff : ∀ a b : X, B a a - B b b = B (a - b) a + B b (a - b))
    (y : X) (hsmall : 4 * C * ‖y‖ < 1) (S : Set X) (hS : IsClosed S) (hyS : y ∈ S)
    (hSmap : ∀ x ∈ S, ‖x‖ ≤ 2 * ‖y‖ → y + B x x ∈ S) :
    ∃ x ∈ S, ‖x‖ ≤ 2 * ‖y‖ ∧ x = y + B x x := by
  set R : ℝ := 2 * ‖y‖ with hR
  set f : X → X := fun x => y + B x x with hf
  set U : Set X := S ∩ Metric.closedBall (0 : X) R with hU
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hUc : IsComplete U := (hS.inter Metric.isClosed_closedBall).isComplete
  have hball : ∀ x : X, x ∈ Metric.closedBall (0 : X) R ↔ ‖x‖ ≤ R := fun x => by
    simp [Metric.mem_closedBall, dist_zero_right]
  have hkey : (4 * C * ‖y‖) * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hsmall.le hy0
  have hmaps : Set.MapsTo f U U := by
    intro x hx
    have hxR : ‖x‖ ≤ R := (hball x).mp hx.2
    refine ⟨hSmap x hx.1 hxR, (hball _).mpr ?_⟩
    have h1 : ‖f x‖ ≤ ‖y‖ + C * (‖x‖ * ‖x‖) :=
      (norm_add_le _ _).trans (by linarith [hB x x])
    have h2 : C * (‖x‖ * ‖x‖) ≤ C * (R * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hxR hxR (norm_nonneg _) (by rw [hR]; positivity))
        hC.le
    have h3 : C * (R * R) = (4 * C * ‖y‖) * ‖y‖ := by rw [hR]; ring
    rw [hR]; linarith
  set K : NNReal := ⟨4 * C * ‖y‖, by positivity⟩ with hK
  have hKcoe : (K : ℝ) = 4 * C * ‖y‖ := rfl
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]; exact hsmall
  have hlip : LipschitzWith K (Set.MapsTo.restrict f _ _ hmaps) := by
    refine LipschitzWith.of_dist_le_mul ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have haR : ‖a‖ ≤ R := (hball a).mp ha.2
    have hbR : ‖b‖ ≤ R := (hball b).mp hb.2
    have hfd : f a - f b = B (a - b) a + B b (a - b) := by
      rw [hf]; simp only [add_sub_add_left_eq_sub]; exact hdiff a b
    have hnorm : ‖f a - f b‖ ≤ C * (‖a - b‖ * ‖a‖) + C * (‖b‖ * ‖a - b‖) := by
      rw [hfd]; exact (norm_add_le _ _).trans (add_le_add (hB _ _) (hB _ _))
    have hab : (0 : ℝ) ≤ ‖a - b‖ := norm_nonneg _
    have hbound : C * (‖a - b‖ * ‖a‖) + C * (‖b‖ * ‖a - b‖)
        ≤ C * (‖a - b‖ * R) + C * (R * ‖a - b‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haR hab) hC.le)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbR hab) hC.le)
    have hRR : C * (‖a - b‖ * R) + C * (R * ‖a - b‖) = (4 * C * ‖y‖) * ‖a - b‖ := by
      rw [hR]; ring
    have hfinal : ‖f a - f b‖ ≤ (4 * C * ‖y‖) * ‖a - b‖ := by linarith
    simpa [Subtype.dist_eq, dist_eq_norm, hKcoe] using hfinal
  have hyU : y ∈ U := ⟨hyS, (hball y).mpr (by rw [hR]; linarith)⟩
  have hedist : edist y (f y) ≠ ⊤ := edist_ne_top _ _
  have hmem := ContractingWith.efixedPoint_mem' hUc hmaps ⟨hK1, hlip⟩ hyU hedist
  have hfix := ContractingWith.efixedPoint_isFixedPt' hUc hmaps ⟨hK1, hlip⟩ hyU hedist
  exact ⟨_, hmem.1, (hball _).mp hmem.2, hfix.symm⟩

/-- Uniqueness of the Picard fixed point in the ball of radius `2‖y‖`. -/
theorem picard_unique {X : Type*} [NormedAddCommGroup X] {B : X → X → X} {C : ℝ}
    (hC : 0 < C) (hB : ∀ a b : X, ‖B a b‖ ≤ C * (‖a‖ * ‖b‖))
    (hdiff : ∀ a b : X, B a a - B b b = B (a - b) a + B b (a - b))
    (y : X) (hsmall : 4 * C * ‖y‖ < 1) {x z : X} (hx : ‖x‖ ≤ 2 * ‖y‖) (hz : ‖z‖ ≤ 2 * ‖y‖)
    (hxe : x = y + B x x) (hze : z = y + B z z) : x = z := by
  have hd : x - z = B (x - z) x + B z (x - z) := by
    rw [← hdiff]
    conv_lhs => rw [hxe, hze]
    abel
  have hn : ‖x - z‖ ≤ (4 * C * ‖y‖) * ‖x - z‖ := by
    have h := (norm_add_le (B (x - z) x) (B z (x - z))).trans (add_le_add (hB _ _) (hB _ _))
    rw [← hd] at h
    have hab : (0 : ℝ) ≤ ‖x - z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hC.le hab),
      mul_le_mul_of_nonneg_left hz (mul_nonneg hC.le hab)]
  have h0 : ‖x - z‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖x - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-! ## The weakly singular Laplace bound -/

theorem integral_rpow_neg_half_exp_le {γ t : ℝ} (hγ : 0 < γ) :
    ∫ σ in Ioc 0 t, σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ)) ≤
      Real.sqrt Real.pi * (1 / γ) ^ (1 / 2 : ℝ) := by
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := γ) (by norm_num) hγ
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at hval
  have hpos : 0 < (1 / γ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by positivity
  have hint : IntegrableOn (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hval]; exact hpos.ne')
  calc ∫ σ in Ioc 0 t, σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ))
      ≤ ∫ σ in Ioi 0, σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ)) := by
        refine setIntegral_mono_set hint ?_ (Ioc_subset_Ioi_self.eventuallyLE)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt hσ) _) (Real.exp_pos _).le
    _ = Real.sqrt Real.pi * (1 / γ) ^ (1 / 2 : ℝ) := by rw [hval, mul_comm]

/-! ## Vector moments -/

/-- Sum of the coordinate moments of a velocity coefficient vector. -/
def momV (n : ℕ) (v : V1) : ℝ≥0∞ := ∑ i : Fin 3, mom n (v i)

theorem lowerSemicontinuous_momV (n : ℕ) : LowerSemicontinuous (momV n) := by
  unfold momV
  exact lowerSemicontinuous_sum fun i _ =>
    lsc_comp_continuous (lowerSemicontinuous_mom n) (continuous_apply i)

theorem mom_le_momV (n : ℕ) (v : V1) (i : Fin 3) : mom n (v i) ≤ momV n v :=
  Finset.single_le_sum (f := fun j => mom n (v j)) (fun _ _ => zero_le) (Finset.mem_univ i)

theorem momV_add_le (n : ℕ) (u v : V1) : momV n (u + v) ≤ momV n u + momV n v := by
  unfold momV
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => mom_add_le n (u i) (v i)

theorem momV_heatOp_le (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) (v : V1) :
    momV n (heatOp ν t v) ≤ momV n v := by
  unfold momV
  refine Finset.sum_le_sum fun i _ => ?_
  rw [heatOp_apply]
  have hb : ∀ᵐ ξ ∂(volume : Measure ES), ‖heatLinf ν t ξ‖ ≤ 1 := by
    filter_upwards [coeFn_heatLinf hν t] with ξ h
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
    exact heatFactor_le_one hν (le_max_right _ _) ξ
  simpa using mom_mulL_le n (heatLinf ν t) hb (v i)

theorem mom_zero_L1C (n : ℕ) : mom n (0 : L1C) = 0 := by
  unfold mom
  have h0 : (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ‖(0 : L1C) ξ‖ₑ) =ᵐ[volume] 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 1 (volume : Measure ES)] with ξ h
    simp
  rw [lintegral_congr_ae h0]
  simp

/-! ## The Duhamel kernel propagates moments -/

theorem mom_kernel_coord_le (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (u : V1) (i : Fin 3) :
    mom n ((kernelOp ν σ (tensorConv u u)) i) ≤
      ENNReal.ofReal ((Real.sqrt (ν * σ))⁻¹) *
        (2 ^ n * (ENNReal.ofReal ‖u‖ * (6 * momV n u))) := by
  set s := ENNReal.ofReal ((Real.sqrt (ν * σ))⁻¹)
  set R := ENNReal.ofReal ‖u‖
  have hb : ∀ j k : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES),
      ‖kernelLinf ν σ i j k ξ‖ ≤ (Real.sqrt (ν * σ))⁻¹ := fun j k => by
    filter_upwards [coeFn_kernelLinf hν hσ i j k] with ξ h
    rw [h]; exact norm_kernelSymbol_le hν hσ i j k ξ
  have hR : ∀ k : Fin 3, mom 0 (u k) ≤ R := fun k => by
    rw [mom_zero]; exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm u k)
  have hterm : ∀ j k : Fin 3, mom n (mulL (kernelLinf ν σ i j k) (conv (u j) (u k))) ≤
      s * (2 ^ n * (R * (mom n (u j) + mom n (u k)))) := by
    intro j k
    refine (mom_mulL_le n _ (hb j k) _).trans ?_
    refine mul_le_mul' le_rfl ((mom_conv_le n (u j) (u k)).trans ?_)
    calc 2 ^ n * (mom n (u j) * mom 0 (u k)) + 2 ^ n * (mom 0 (u j) * mom n (u k))
        ≤ 2 ^ n * (mom n (u j) * R) + 2 ^ n * (R * mom n (u k)) := by
          gcongr
          · exact hR k
          · exact hR j
      _ = 2 ^ n * (R * (mom n (u j) + mom n (u k))) := by ring
  rw [kernelOp, tensorMulOp_apply]
  simp only [tensorConv_apply]
  refine (mom_sum_le n _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => (mom_sum_le n _ _).trans
    (Finset.sum_le_sum fun k _ => hterm j k)).trans (le_of_eq ?_)
  unfold momV
  simp only [Fin.sum_univ_three]
  ring

/-! ## Invariance of moment sets under the Picard map -/

section Invariance

variable {ν T : ℝ}

/-- Paths whose `n`-th vector moment grows at most like `M e^{γt}`. -/
def momSet (n : ℕ) (M γ : ℝ) : Set C(Icc (0 : ℝ) T, V1) :=
  {y | ∀ t : Icc (0 : ℝ) T, momV n (y t) ≤ ENNReal.ofReal (M * Real.exp (γ * t))}

theorem isClosed_momSet (n : ℕ) (M γ : ℝ) : IsClosed (momSet (T := T) n M γ) := by
  have h : momSet (T := T) n M γ = ⋂ t : Icc (0 : ℝ) T,
      (fun y : C(Icc (0 : ℝ) T, V1) => momV n (y t)) ⁻¹'
        Iic (ENNReal.ofReal (M * Real.exp (γ * t))) := by
    ext y; simp [momSet]
  rw [h]
  exact isClosed_iInter fun t =>
    (lsc_comp_continuous (lowerSemicontinuous_momV n)
      (continuous_eval_const t)).isClosed_preimage _

/-- The majorant of the `n`-th moment of the Duhamel integrand at time `t`. -/
def momMajorant (ν : ℝ) (n : ℕ) (K M γ t : ℝ) (σ : ℝ) : ℝ :=
  (Ioc 0 t).indicator
    (fun σ => singWeight ν σ * (2 ^ n * (K * (6 * (M * Real.exp (γ * (t - σ))))))) σ

theorem momMajorant_nonneg (ν : ℝ) (n : ℕ) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (γ t σ : ℝ) :
    0 ≤ momMajorant ν n K M γ t σ := by
  unfold momMajorant
  refine Set.indicator_nonneg (fun σ hσ => ?_) σ
  have := singWeight_nonneg ν σ hσ.1.le
  positivity

theorem integral_momMajorant_eq (ν : ℝ) (n : ℕ) (K M γ : ℝ) {t : ℝ} (htT : t ≤ T) :
    ∫ σ in Ioc 0 T, momMajorant ν n K M γ t σ =
      ((Real.sqrt ν)⁻¹ * (2 ^ n * (K * (6 * (M * Real.exp (γ * t)))))) *
        ∫ σ in Ioc 0 t, σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ)) := by
  unfold momMajorant
  rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_right htT,
    ← integral_const_mul]
  congr 1
  funext σ
  unfold singWeight
  rw [mul_sub, Real.exp_sub, Real.exp_neg]
  field_simp

theorem integrableOn_momMajorant (ν : ℝ) (n : ℕ) {K M γ : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hγ : 0 ≤ γ) (hT0 : 0 ≤ T) (t : ℝ) :
    IntegrableOn (momMajorant ν n K M γ t) (Ioc 0 T) := by
  have hbase : IntegrableOn
      (fun σ => singWeight ν σ * (2 ^ n * (K * (6 * (M * Real.exp (γ * t)))))) (Ioc 0 T) :=
    (integrableOn_singWeight ν hT0).mul_const _
  refine hbase.mono' ?_ ?_
  · unfold momMajorant singWeight
    refine (Measurable.indicator ?_ measurableSet_Ioc).aestronglyMeasurable
    exact (measurable_const.mul (measurable_id.pow_const _)).mul
      (measurable_const.mul (measurable_const.mul (measurable_const.mul
        (measurable_const.mul (Real.continuous_exp.measurable.comp
          (measurable_const.mul (measurable_const.sub measurable_id)))))))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (momMajorant_nonneg ν n hK hM γ t σ)]
    unfold momMajorant
    by_cases hs : σ ∈ Ioc 0 t
    · rw [Set.indicator_of_mem hs]
      have hw := singWeight_nonneg ν σ hσ.1.le
      have he : Real.exp (γ * (t - σ)) ≤ Real.exp (γ * t) :=
        Real.exp_le_exp.mpr (by nlinarith [hσ.1])
      gcongr
    · rw [Set.indicator_of_notMem hs]
      have hw := singWeight_nonneg ν σ hσ.1.le
      positivity

/-- **Moment bound for one coordinate of the Duhamel term.** -/
theorem mom_duhamel_coord_le (n : ℕ) (hν : 0 < ν) (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1))
    {M γ : ℝ} (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hy : y ∈ momSet n M γ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    mom n ((duhamel ν hT0 y y t) i) ≤
      ENNReal.ofReal (∫ σ in Ioc 0 T, momMajorant ν n ‖y‖ M γ t σ) := by
  have hint := integrable_duhIntegrand hν hT0 y y t
  have hcoord : (duhamel ν hT0 y y t) i = ∫ σ in Ioc 0 T, duhIntegrand ν hT0 y y t σ i := by
    unfold duhamel
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integral_comp_comm
      hint).symm
  rw [hcoord]
  refine mom_integral_le n _
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integrable_comp hint)
    _ (integrableOn_momMajorant ν n (norm_nonneg y) hM hγ hT0 t)
    (momMajorant_nonneg ν n (norm_nonneg y) hM γ t) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
  by_cases hle : σ ≤ t
  · have hdi : duhIntegrand ν hT0 y y t σ =
        kernelOp ν σ (tensorConv (extend hT0 y (t - σ)) (extend hT0 y (t - σ))) := by
      unfold duhIntegrand
      exact Set.indicator_of_mem (show σ ∈ Iic t from hle) _
    have hmem : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hσ.1, ht.2]⟩
    have hext : extend hT0 y (t - σ) = y ⟨t - σ, hmem⟩ := by
      unfold WienerLocalMild.extend; rw [projIcc_of_mem hT0 hmem]
    have hmomy : momV n (extend hT0 y (t - σ)) ≤
        ENNReal.ofReal (M * Real.exp (γ * (t - σ))) := by
      rw [hext]; exact hy ⟨t - σ, hmem⟩
    rw [hdi]
    unfold momMajorant
    rw [Set.indicator_of_mem (show σ ∈ Ioc 0 t from ⟨hσ.1, hle⟩)]
    have hs0 : 0 ≤ singWeight ν σ := singWeight_nonneg ν σ hσ.1.le
    have hX : 0 ≤ M * Real.exp (γ * (t - σ)) := by positivity
    have e : ENNReal.ofReal (singWeight ν σ *
        (2 ^ n * (‖y‖ * (6 * (M * Real.exp (γ * (t - σ))))))) =
        ENNReal.ofReal (singWeight ν σ) * (2 ^ n * (ENNReal.ofReal ‖y‖ *
          (6 * ENNReal.ofReal (M * Real.exp (γ * (t - σ)))))) := by
      rw [ENNReal.ofReal_mul hs0, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [e]
    refine (mom_kernel_coord_le n hν hσ.1 _ i).trans ?_
    rw [sqrt_mul_inv_eq_singWeight hν hσ.1]
    gcongr
    exact norm_extend_le hT0 y _
  · have h0 : duhIntegrand ν hT0 y y t σ = 0 := by
      unfold duhIntegrand
      exact Set.indicator_of_notMem (show σ ∉ Iic t from hle) _
    rw [h0, map_zero, mom_zero_L1C]
    exact zero_le

/-- The exponential rate used for the `n`-th moment. -/
def momRate (ν : ℝ) (n : ℕ) (a₀ : V1) : ℝ :=
  (36 * 2 ^ n * (2 * ‖a₀‖) * Real.sqrt Real.pi * (Real.sqrt ν)⁻¹ + 1) ^ 2

theorem mapsTo_momSet (n : ℕ) (hν : 0 < ν) (hT : 0 < T) (a₀ : V1) {m : ℝ} (hm0 : 0 ≤ m)
    (hma : momV n a₀ ≤ ENNReal.ofReal m) (y : C(Icc (0 : ℝ) T, V1))
    (hy : y ∈ momSet n (2 * m) (momRate ν n a₀)) (hyn : ‖y‖ ≤ 2 * ‖a₀‖) :
    heatPath hν a₀ + duhamelPath hν hT.le y y ∈ momSet n (2 * m) (momRate ν n a₀) := by
  intro t
  set a : ℝ := 36 * 2 ^ n * (2 * ‖a₀‖) * Real.sqrt Real.pi * (Real.sqrt ν)⁻¹ with ha
  set γ : ℝ := momRate ν n a₀ with hγdef
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hγ : γ = (a + 1) ^ 2 := rfl
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) T := t.2
  have hval : (heatPath hν a₀ + duhamelPath hν hT.le y y : C(Icc (0 : ℝ) T, V1)) t =
      heatOp ν t a₀ + duhamel ν hT.le y y t := rfl
  rw [hval]
  set I : ℝ := ∫ σ in Ioc 0 T, momMajorant ν n ‖y‖ (2 * m) γ t σ with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun σ _ =>
    momMajorant_nonneg ν n (norm_nonneg y) (by positivity) γ t σ
  have hD : momV n (duhamel ν hT.le y y t) ≤ 3 * ENNReal.ofReal I := by
    unfold momV
    simp only [Fin.sum_univ_three]
    have hc := fun i => mom_duhamel_coord_le n hν hT.le y (M := 2 * m) (by positivity)
      hγ0.le hy ht i
    calc mom n (duhamel ν hT.le y y t 0) + mom n (duhamel ν hT.le y y t 1) +
          mom n (duhamel ν hT.le y y t 2)
        ≤ ENNReal.ofReal I + ENNReal.ofReal I + ENNReal.ofReal I := by
          gcongr
          · exact hc 0
          · exact hc 1
          · exact hc 2
      _ = 3 * ENNReal.ofReal I := by ring
  -- the real estimate
  have hrt : (1 / γ) ^ (1 / 2 : ℝ) = 1 / (a + 1) := by
    rw [← Real.sqrt_eq_rpow, hγ, one_div, Real.sqrt_inv, Real.sqrt_sq (by positivity), one_div]
  set E : ℝ := Real.exp (γ * t) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by nlinarith [ht.1])
  have hIeq := integral_momMajorant_eq (T := T) ν n ‖y‖ (2 * m) γ ht.2
  have hJ := integral_rpow_neg_half_exp_le (t := (t : ℝ)) hγ0
  rw [hrt] at hJ
  have hJ0 : 0 ≤ ∫ σ in Ioc 0 (t : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ)) :=
    setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg hσ.1.le _) (Real.exp_pos _).le
  have h3I : 3 * I ≤ m * E := by
    rw [hI, hIeq]
    have hK0 : 0 ≤ (Real.sqrt ν)⁻¹ * (2 ^ n * (‖y‖ * (6 * (2 * m * E)))) := by positivity
    calc 3 * ((Real.sqrt ν)⁻¹ * (2 ^ n * (‖y‖ * (6 * (2 * m * E)))) *
          ∫ σ in Ioc 0 (t : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(γ * σ)))
        ≤ 3 * ((Real.sqrt ν)⁻¹ * (2 ^ n * (‖y‖ * (6 * (2 * m * E)))) *
            (Real.sqrt Real.pi * (1 / (a + 1)))) := by gcongr
      _ ≤ 3 * ((Real.sqrt ν)⁻¹ * (2 ^ n * ((2 * ‖a₀‖) * (6 * (2 * m * E)))) *
            (Real.sqrt Real.pi * (1 / (a + 1)))) := by gcongr
      _ = a * (m * E) / (a + 1) := by rw [ha]; field_simp; ring
      _ ≤ m * E := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ E)]
  have hreal : m + 3 * I ≤ 2 * m * E := by nlinarith
  calc momV n (heatOp ν t a₀ + duhamel ν hT.le y y t)
      ≤ momV n (heatOp ν t a₀) + momV n (duhamel ν hT.le y y t) := momV_add_le n _ _
    _ ≤ ENNReal.ofReal m + 3 * ENNReal.ofReal I :=
        add_le_add ((momV_heatOp_le n hν.le t a₀).trans hma) hD
    _ = ENNReal.ofReal (m + 3 * I) := by
        rw [ENNReal.ofReal_add hm0 (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 * m * Real.exp (γ * t)) := ENNReal.ofReal_le_ofReal hreal

end Invariance

/-! ## Large-data local existence with every Fourier moment propagated -/

/-- **Large-data local mild existence with moment propagation.**  The unique
Picard fixed point in the ball of radius `2‖a₀‖` carries, for every `n` for
which the datum has a finite `n`-th moment `≤ m`, the bound
`momV n (x t) ≤ 2m·exp(γₙ t)` on the whole horizon, with an explicit rate
`γₙ = momRate ν n a₀`.  No smallness of any moment is assumed, and the horizon
is the same for every `n`. -/
theorem exists_wienerMildSolution_moments {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1), ‖x‖ ≤ 2 * ‖a₀‖ ∧
      x = heatPath hν a₀ + duhamelPath hν hT.le x x ∧
      ∀ (n : ℕ) (m : ℝ), 0 ≤ m → momV n a₀ ≤ ENNReal.ofReal m →
        x ∈ momSet n (2 * m) (momRate ν n a₀) := by
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T with hC
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hC0 : 0 < C := by rw [hC]; positivity
  set y : C(Icc (0 : ℝ) T, V1) := heatPath hν a₀ with hy
  have hyle : ‖y‖ ≤ ‖a₀‖ := norm_heatPath_le hν a₀
  have hroot : 100 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [show (10 : ℝ) ^ 4 * T * ‖a₀‖ ^ 2 = (100 * (Real.sqrt T * ‖a₀‖)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]; ring,
      Real.sqrt_sq (by positivity)] at h
  have hsmallC : 4 * C * ‖y‖ < 1 := by
    have h1 : 4 * C * ‖y‖ ≤ 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν := by
      rw [hC, div_eq_mul_inv]
      have : 4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖y‖ ≤
          4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖a₀‖ :=
        mul_le_mul_of_nonneg_left hyle (by positivity)
      nlinarith [this]
    have h2 : 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν < 1 := by
      rw [div_lt_one hsν]
      have : 0 ≤ Real.sqrt T * ‖a₀‖ := by positivity
      nlinarith
    linarith
  have hB := norm_duhamelPath_le hν hT.le
  have hdiff := duhamelPath_diff hν hT.le
  obtain ⟨x, -, hxle, hxeq⟩ := picard_small_data_on hC0 hB hdiff y hsmallC Set.univ
    isClosed_univ (Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
  refine ⟨x, hxle.trans (by linarith), hxeq, fun n m hm0 hma => ?_⟩
  have hyS : y ∈ momSet n (2 * m) (momRate ν n a₀) := by
    intro t
    have hE : 1 ≤ Real.exp (momRate ν n a₀ * t) :=
      Real.one_le_exp (mul_nonneg (by unfold momRate; positivity) t.2.1)
    calc momV n (y t) = momV n (heatOp ν t a₀) := rfl
      _ ≤ momV n a₀ := momV_heatOp_le n hν.le t a₀
      _ ≤ ENNReal.ofReal m := hma
      _ ≤ ENNReal.ofReal (2 * m * Real.exp (momRate ν n a₀ * t)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
  obtain ⟨xn, hxnS, hxnle, hxneq⟩ := picard_small_data_on hC0 hB hdiff y hsmallC
    (momSet n (2 * m) (momRate ν n a₀)) (isClosed_momSet n _ _) hyS
    (fun z hz hzn => mapsTo_momSet n hν hT a₀ hm0 hma z hz (hzn.trans (by linarith)))
  have hxx : xn = x := picard_unique hC0 hB hdiff y hsmallC hxnle hxle hxneq hxeq
  rw [← hxx]
  exact hxnS

end Navier.Analysis.WienerMoments

set_option pp.fullNames true in
#check @Navier.Analysis.WienerMoments.exists_wienerMildSolution_moments
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerMoments.exists_wienerMildSolution_moments
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerMoments.mom_conv_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerMoments.mapsTo_momSet
