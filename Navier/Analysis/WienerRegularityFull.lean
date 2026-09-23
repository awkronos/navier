import Navier.Analysis.WienerRegularity
import Navier.Analysis.WienerPressureSmooth
import Navier.Analysis.WienerLinfBound

/-!
# The Wiener pair lies in the full regular class `R`

Beyond the velocity slices (`WienerRegularity.regSlice_physU`), the pressure
gradient is in `H¹` and `∂ₜu` is in `L²`, uniformly on `[0,T)`: both are inverse
transforms of Fourier coefficients with an `L∞`-type pointwise bound and a
time-uniform majorant with all moments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate Topology

namespace Navier.Analysis.WienerRegularityFull

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerPhysicalPDE
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.WienerLocalClassical
open Navier.Analysis.WienerRegularity
open Navier.Analysis.WienerPressureSmooth
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition (CriticalQuantity)

/-- **`L²` of an inverse transform from a squared pointwise bound.** -/
theorem l2_fourierInv_of_sq_bound {f : ES → ℂ} (hfm : StronglyMeasurable f)
    (hfi : Integrable f) {G : ES → ℝ≥0∞} (hG : ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ₑ ^ 2 ≤ G ξ)
    (hfin : ∫⁻ ξ, G ξ ≠ ⊤) :
    Integrable (fun y => ‖𝓕⁻ f y‖ ^ 2) ∧ (∫ y, ‖𝓕⁻ f y‖ ^ 2) ≤ (∫⁻ ξ, G ξ).toReal := by
  have hPl := (Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le hfm hfi).trans
    (lintegral_mono_ae hG)
  have hint := integrable_norm_sq_of_lintegral (continuous_fourierInv hfi)
    (ne_top_of_le_ne_top hfin hPl)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_mono hfin (le_trans (le_of_eq (lintegral_congr fun y => ?_)) hPl)
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `|-(c) Re(a z)| ≤ c ‖a‖ ‖z‖`. -/
theorem abs_neg_mul_re_le (c : ℝ) (hc : 0 ≤ c) (a z : ℂ) :
    |-c * (a * z).re| ≤ c * (‖a‖ * ‖z‖) := by
  rw [abs_mul, abs_neg, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (by rw [norm_mul])) hc

theorem norm_two_pi_I : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  rw [norm_mul, Complex.norm_I, mul_one,
    show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

section Full

variable {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
  {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w) {R : ℝ} (hR0 : 0 ≤ R)
  (hRb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖w t ξ‖ ≤ R)

include hT hν hG hR0 hRb in
/-- **A uniform bound on the pressure coefficient.** -/
theorem qhat_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, ‖Qhat w t ξ‖ ≤ Cq := by
  have hGc := hG
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hGc
  have hMf : ∫⁻ ξ, M ξ ≠ ⊤ := lintegral_ne_top_of_mom hmom
  refine ⟨9 * (R * (∫⁻ ξ, M ξ).toReal), by positivity, fun t ht ξ => ?_⟩
  have hint : ∀ j : Fin 3, Integrable (fun η => w t η j) := fun j =>
    integrable_of_hmom (hmom_w hT hν hG ht j)
  have hL1 : ∀ j : Fin 3, ∫ η, ‖w t η j‖ ≤ (∫⁻ ξ, M ξ).toReal := by
    intro j
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun η => norm_nonneg _)
      (hint j).norm.aestronglyMeasurable]
    refine ENNReal.toReal_mono hMf (lintegral_mono_ae ?_)
    filter_upwards [hb] with η h
    rw [ofReal_norm]
    exact (enorm_coord_le _ j).trans (h t ht)
  have hcc : ∀ j k : Fin 3, ‖cc w t j k ξ‖ ≤ R * (∫⁻ ξ, M ξ).toReal := by
    intro j k
    unfold cc
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    refine (norm_integral_le_of_norm_le ((hint j).norm.mul_const R) ?_).trans ?_
    · filter_upwards [ae_sub_left hRb ξ] with η h
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ k).trans (h t ht)) (norm_nonneg _)
    · rw [integral_mul_const, mul_comm]
      exact mul_le_mul_of_nonneg_left (hL1 j) hR0
  refine (norm_Qhat_le t ξ).trans ?_
  calc ∑ j : Fin 3, ∑ k : Fin 3, ‖cc w t j k ξ‖
      ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, R * (∫⁻ ξ, M ξ).toReal :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hcc j k
    _ = 9 * (R * (∫⁻ ξ, M ξ).toReal) := by simp; ring

include hT hν hG hR0 hRb in
/-- **Uniform `L²` bounds for the pressure multipliers.** -/
theorem l2_bound_Q :
    ∃ BQ : ℕ → ℝ, (∀ n, 0 ≤ BQ n) ∧ ∀ (α : Fin 3 → ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      Integrable (fun y => ‖𝓕⁻ (fun ξ => mono α ξ * Qhat w t ξ) y‖ ^ 2) ∧
      (∫ y, ‖𝓕⁻ (fun ξ => mono α ξ * Qhat w t ξ) y‖ ^ 2) ≤ BQ (2 * deg α) := by
  obtain ⟨Cq, hCq0, hCq⟩ := qhat_bound hT hν hG hR0 hRb
  obtain ⟨-, MQ, hMQ, hbQ, hmomQ, -⟩ := good_Pk hν.le hG 0
  refine ⟨fun n => (ENNReal.ofReal Cq * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * MQ ξ).toReal,
    fun n => ENNReal.toReal_nonneg, fun α t ht => ?_⟩
  have hPm : StronglyMeasurable (fun ξ => Pk ν w 0 t ξ 0) :=
    (continuous_apply 0).comp_stronglyMeasurable ((good_Pk hν.le hG 0).1 t)
  have hQm : StronglyMeasurable (Qhat w t) := by
    have : Qhat w t = fun ξ => Pk ν w 0 t ξ 0 := funext (Qhat_eq_Pk_zero ν w t)
    rw [this]; exact hPm
  have hfm : StronglyMeasurable (fun ξ => mono α ξ * Qhat w t ξ) :=
    ((by unfold mono; fun_prop : Continuous (mono α)).stronglyMeasurable).mul hQm
  have hfi : Integrable (fun ξ => mono α ξ * Qhat w t ξ) := hmom_Qhat hG ht α
  have hbd : ∀ᵐ ξ ∂(volume : Measure ES), ‖mono α ξ * Qhat w t ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal Cq * (ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * MQ ξ) := by
    filter_upwards [hbQ] with ξ h
    have e1 : ‖Qhat w t ξ‖ₑ ≤ MQ ξ := by
      rw [Qhat_eq_Pk_zero ν w t ξ]; exact (enorm_coord_le _ 0).trans (h t ht)
    have e2 : ‖Qhat w t ξ‖ₑ ≤ ENNReal.ofReal Cq := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCq t ht ξ)
    have e3 : ‖mono α ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [pow_mul, ← pow_mul, mul_comm 2 (deg α), pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_mono_le α ξ) 2
    calc ‖mono α ξ * Qhat w t ξ‖ₑ ^ 2 = ‖mono α ξ‖ₑ ^ 2 * (‖Qhat w t ξ‖ₑ * ‖Qhat w t ξ‖ₑ) := by
          simp only [enorm_mul]; ring
      _ ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * (ENNReal.ofReal Cq * MQ ξ) :=
          mul_le_mul' e3 (mul_le_mul' e2 e1)
      _ = ENNReal.ofReal Cq * (ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * MQ ξ) := by ring
  have hfin : ∫⁻ ξ, ENNReal.ofReal Cq * (ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * MQ ξ) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmomQ _)
  have key := l2_fourierInv_of_sq_bound hfm hfi hbd hfin
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  show _ = (ENNReal.ofReal Cq * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * MQ ξ).toReal
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

include hT hν hG in
theorem fderiv_physP_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    (fun x => fderiv ℝ (physP w t) x (basisVector i)) = fun x =>
      -(1 / (4 * Real.pi ^ 2)) * ((2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ => mono (ej i) ξ * Qhat w t ξ) (euclidPoint x)).re := by
  funext x
  have hq := hmom_Qhat hG ht
  rw [show physP w t = fun x' : Space =>
      -(1 / (4 * Real.pi ^ 2)) * (𝓕⁻ (Qhat w t) (euclidPoint x')).re from rfl,
    fderiv_reComp_apply (fun y => differentiable_fourierInv hq y), euclidPoint_basisVector,
    fderiv_fourierInv_single (integrable_of_hmom hq) (integrable_coord_mul hq) _ i]
  rw [show (fun ξ : ES => ((ξ i : ℝ) : ℂ) * Qhat w t ξ) = fun ξ => mono (ej i) ξ * Qhat w t ξ
    from funext fun ξ => by rw [mono_ej]]

include hT hν hG in
theorem fderiv2_physP_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i j : Fin 3) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ (physP w t) y (basisVector i)) x (basisVector j)) =
      fun x => -(1 / (4 * Real.pi ^ 2)) * ((2 * Real.pi : ℂ) * Complex.I *
        ((2 * Real.pi : ℂ) * Complex.I *
          𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * Qhat w t ξ) (euclidPoint x))).re := by
  have hq := hmom_Qhat hG ht
  have hin : (fun y => fderiv ℝ (physP w t) y (basisVector i)) = fun y : Space =>
      -(1 / (4 * Real.pi ^ 2)) *
        ((fun z => fderiv ℝ (𝓕⁻ (Qhat w t)) z (EuclideanSpace.single i 1)) (euclidPoint y)).re := by
    funext y
    rw [show physP w t = fun x' : Space =>
        -(1 / (4 * Real.pi ^ 2)) * (𝓕⁻ (Qhat w t) (euclidPoint x')).re from rfl,
      fderiv_reComp_apply (fun y => differentiable_fourierInv hq y), euclidPoint_basisVector]
  funext x
  rw [hin, fderiv_reComp_apply (fun y => differentiable_fderiv_fourierInv hq i y),
    euclidPoint_basisVector, fderiv_fderiv_fourierInv_single hq j i]
  rw [show (fun ξ : ES => ((ξ j : ℝ) : ℂ) * (((ξ i : ℝ) : ℂ) * Qhat w t ξ)) =
      fun ξ => mono (ej i + ej j) ξ * Qhat w t ξ from
    funext fun ξ => by rw [mono_ej_ej]; ring]

include hT hν hG hR0 hRb in
/-- **The pressure is in `H¹`-gradient class, uniformly on `[0,T]`.** -/
theorem presSlice_physP : ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T, PresSlice K (physP w t) := by
  obtain ⟨BQ, hBQ0, hBQ⟩ := l2_bound_Q hT hν hG hR0 hRb
  set K : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, (BQ (2 * deg (ej i)) + BQ (2 * deg (ej i + ej j)))
  have hnn : ∀ i j : Fin 3, 0 ≤ BQ (2 * deg (ej i)) + BQ (2 * deg (ej i + ej j)) := fun i j => by
    have := hBQ0 (2 * deg (ej i)); have := hBQ0 (2 * deg (ej i + ej j)); positivity
  refine ⟨K, fun t ht i j => ?_⟩
  have hle : BQ (2 * deg (ej i)) + BQ (2 * deg (ej i + ej j)) ≤ K := by
    calc _ ≤ ∑ j' : Fin 3, (BQ (2 * deg (ej i)) + BQ (2 * deg (ej i + ej j'))) :=
          Finset.single_le_sum (f := fun j' => BQ (2 * deg (ej i)) + BQ (2 * deg (ej i + ej j')))
            (fun j' _ => hnn i j') (Finset.mem_univ j)
      _ ≤ K := Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3,
            (BQ (2 * deg (ej i')) + BQ (2 * deg (ej i' + ej j'))))
            (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)
  have hq := hmom_Qhat hG ht
  have hπ : 0 < Real.pi := Real.pi_pos
  -- first derivative
  set g1 : Space → ℝ := fun x => ‖𝓕⁻ (fun ξ => mono (ej i) ξ * Qhat w t ξ) (euclidPoint x)‖ ^ 2
  have hg1i : Integrable g1 := integrable_space_euclid (hBQ (ej i) t ht).1
  have hg1v : ∫ x, g1 x ≤ BQ (2 * deg (ej i)) := by
    rw [integral_space_euclid (fun y => ‖𝓕⁻ (fun ξ => mono (ej i) ξ * Qhat w t ξ) y‖ ^ 2)]
    exact (hBQ (ej i) t ht).2
  have hF1 := fderiv_physP_eq hT hν hG ht i
  have hc1 : Continuous (fun x => fderiv ℝ (physP w t) x (basisVector i)) := by
    rw [hF1]
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul
      ((continuous_fourierInv (hq (ej i))).comp (PiLp.continuous_toLp 2 _))))
  have hb1 : ∀ x, ‖fderiv ℝ (physP w t) x (basisVector i)‖ ^ 2 ≤ g1 x := by
    intro x
    have := congrFun hF1 x
    rw [this, Real.norm_eq_abs, ← sq_abs, sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_neg_mul_re_le _ (by positivity) _ _).trans ?_) 2
    rw [norm_two_pi_I]
    have : 1 / (4 * Real.pi ^ 2) * (2 * Real.pi) ≤ 1 := by
      rw [show 1 / (4 * Real.pi ^ 2) * (2 * Real.pi) = 1 / (2 * Real.pi) by field_simp; ring]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    calc 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * ‖_‖) =
          (1 / (4 * Real.pi ^ 2) * (2 * Real.pi)) * ‖𝓕⁻ (fun ξ => mono (ej i) ξ * Qhat w t ξ)
            (euclidPoint x)‖ := by ring
      _ ≤ 1 * ‖𝓕⁻ (fun ξ => mono (ej i) ξ * Qhat w t ξ) (euclidPoint x)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  have hI1 : Integrable (fun x : Space => ‖fderiv ℝ (physP w t) x (basisVector i)‖ ^ 2) :=
    hg1i.mono' ((continuous_norm.comp hc1).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb1 x)
  -- second derivative
  set g2 : Space → ℝ := fun x =>
    ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * Qhat w t ξ) (euclidPoint x)‖ ^ 2
  have hg2i : Integrable g2 := integrable_space_euclid (hBQ (ej i + ej j) t ht).1
  have hg2v : ∫ x, g2 x ≤ BQ (2 * deg (ej i + ej j)) := by
    rw [integral_space_euclid (fun y =>
      ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * Qhat w t ξ) y‖ ^ 2)]
    exact (hBQ (ej i + ej j) t ht).2
  have hF2 := fderiv2_physP_eq hT hν hG ht i j
  have hc2 : Continuous (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (physP w t) y (basisVector i)) x (basisVector j)) := by
    rw [hF2]
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul
      (continuous_const.mul ((continuous_fourierInv (hq (ej i + ej j))).comp
        (PiLp.continuous_toLp 2 _)))))
  have hb2 : ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (physP w t) y (basisVector i)) x
      (basisVector j)‖ ^ 2 ≤ g2 x := by
    intro x
    have := congrFun hF2 x
    rw [this, Real.norm_eq_abs, ← sq_abs, sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_neg_mul_re_le _ (by positivity) _ _).trans ?_) 2
    rw [norm_two_pi_I, norm_mul ((2 * Real.pi : ℂ) * Complex.I), norm_two_pi_I]
    have : 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * (2 * Real.pi)) = 1 := by field_simp; ring
    refine le_of_eq ?_
    calc 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * (2 * Real.pi * ‖_‖)) =
          (1 / (4 * Real.pi ^ 2) * (2 * Real.pi * (2 * Real.pi))) *
            ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * Qhat w t ξ) (euclidPoint x)‖ := by ring
      _ = _ := by rw [this, one_mul]
  have hI2 : Integrable (fun x : Space =>
      ‖fderiv ℝ (fun y => fderiv ℝ (physP w t) y (basisVector i)) x (basisVector j)‖ ^ 2) :=
    hg2i.mono' ((continuous_norm.comp hc2).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb2 x)
  have e1 := hBQ0 (2 * deg (ej i)); have e2 := hBQ0 (2 * deg (ej i + ej j))
  refine ⟨hI1, ?_, hI2, ?_⟩
  · exact (integral_mono hI1 hg1i hb1).trans (hg1v.trans (by linarith))
  · exact (integral_mono hI2 hg2i hb2).trans (hg2v.trans (by linarith))

include hT hν hfix hG in
/-- The time derivative of the rescaled velocity is the inverse transform of `W 1`. -/
theorem timeDerivative_physU_eq {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) (x : Space) :
    timeDerivative (physU w) t x = fun k =>
      -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)).re := by
  have hnhds : Ico (0 : ℝ) T ∈ 𝓝[Ici (0 : ℝ)] t := by
    rw [← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds htT)
  have hk : ∀ k : Fin 3, HasDerivWithinAt (fun s => physU w s x k)
      (-(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)).re)
      (Ici (0 : ℝ)) t := by
    intro k
    have h := hasDerivWithinAt_physTime hT hν a hfix hG k (euclidPoint x) ⟨ht0, htT⟩
    have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t h).const_mul
      (-(1 / (2 * Real.pi)))
    exact h2.mono_of_mem_nhdsWithin hnhds
  exact (hasDerivWithinAt_pi.2 hk).derivWithin (uniqueDiffOn_Ici 0 t ht0)

include hT hν hG hR0 hRb in
/-- **Uniform `L²` bound for the inverse transform of `W 1`.** -/
theorem l2_bound_W1 :
    ∃ BT : ℝ, 0 ≤ BT ∧ ∀ (k : Fin 3) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      Integrable (fun y => ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) y‖ ^ 2) ∧
      (∫ y, ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) y‖ ^ 2) ≤ BT := by
  have hGc := hG
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hGc
  obtain ⟨hm1, M1, hM1, hb1, hmom1, -⟩ := good_W hν.le hG 1
  have hMf : ∫⁻ ξ, M ξ ≠ ⊤ := lintegral_ne_top_of_mom hmom
  set B : ℝ := (∫⁻ ξ, M ξ).toReal with hB
  set C1 : ℝ := ν * R + 27 * R * B with hC1def
  have hC1 : 0 ≤ C1 := by positivity
  set G : ES → ℝ≥0∞ := fun ξ => ENNReal.ofReal C1 * (M1 ξ + ENNReal.ofReal (‖ξ‖ ^ 2) * M1 ξ)
  have hGfin : ∫⁻ ξ, G ξ ≠ ⊤ := by
    have h0 := hmom1 0
    simp only [pow_zero, ENNReal.ofReal_one, one_mul] at h0
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hM1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨h0, hmom1 2⟩)
  refine ⟨(∫⁻ ξ, G ξ).toReal, ENNReal.toReal_nonneg, fun k t ht => ?_⟩
  have hfm : StronglyMeasurable (fun ξ => W ν w 1 t ξ k) :=
    (continuous_apply k).comp_stronglyMeasurable (hm1 t)
  have hfi : Integrable (fun ξ => W ν w 1 t ξ k) :=
    integrable_of_hmom (fun α => integrable_moment hT hν hG 1 α ht k)
  refine l2_fourierInv_of_sq_bound hfm hfi ?_ hGfin
  have hRs : ∀ᵐ ζ ∂(volume : Measure ES), ‖w t ζ‖ ≤ R := by
    filter_upwards [hRb] with ζ h using h t ht
  have hL : ∫⁻ η, ‖w t η‖ₑ ≤ 3 * ENNReal.ofReal B := by
    calc ∫⁻ η, ‖w t η‖ₑ ≤ ∫⁻ η, M η := lintegral_mono_ae (by
          filter_upwards [hb] with η h using h t ht)
      _ = ENNReal.ofReal B := by rw [hB, ENNReal.ofReal_toReal hMf]
      _ ≤ 3 * ENNReal.ofReal B := by
          calc ENNReal.ofReal B = 1 * ENNReal.ofReal B := (one_mul _).symm
            _ ≤ 3 * ENNReal.ofReal B := mul_le_mul' (by norm_num) le_rfl
  filter_upwards [hb1, hRs] with ξ h1 h2
  have hbil := Navier.Analysis.WienerLinfBound.enorm_bil_le_of_bound (w t) hR0 hRs hL ξ
  have hbil' : ‖continuousNavierBilinear (w t) (w t) ξ k‖ ≤ ‖ξ‖ * (27 * R * B) := by
    rw [← ofReal_norm] at hbil
    exact (norm_le_pi_norm _ k).trans ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbil)
  have hpt : ‖W ν w 1 t ξ k‖ ≤ C1 * (1 + ‖ξ‖ ^ 2) := by
    rw [W_one]
    refine (norm_add_le _ _).trans ?_
    have hh : ‖heatSym2 ν ξ * w t ξ k‖ ≤ ν * ‖ξ‖ ^ 2 * R := by
      unfold heatSym2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ k).trans h2) (by positivity)
    have hξ : ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg (‖ξ‖ - 1)]
    have h27 : 0 ≤ 27 * R * B := by positivity
    calc ‖heatSym2 ν ξ * w t ξ k‖ + ‖continuousNavierBilinear (w t) (w t) ξ k‖
        ≤ ν * ‖ξ‖ ^ 2 * R + ‖ξ‖ * (27 * R * B) := add_le_add hh hbil'
      _ ≤ ν * R * (1 + ‖ξ‖ ^ 2) + 27 * R * B * (1 + ‖ξ‖ ^ 2) := by
          have : 0 ≤ ν * R := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hξ h27]
      _ = C1 * (1 + ‖ξ‖ ^ 2) := by rw [hC1def]; ring
  have e1 : ‖W ν w 1 t ξ k‖ₑ ≤ M1 ξ := (enorm_coord_le _ k).trans (h1 t ht)
  have e2 : ‖W ν w 1 t ξ k‖ₑ ≤ ENNReal.ofReal C1 * (1 + ENNReal.ofReal (‖ξ‖ ^ 2)) := by
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hpt).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hC1, ENNReal.ofReal_add zero_le_one (by positivity),
      ENNReal.ofReal_one]
  calc ‖W ν w 1 t ξ k‖ₑ ^ 2 = ‖W ν w 1 t ξ k‖ₑ * ‖W ν w 1 t ξ k‖ₑ := sq _
    _ ≤ ENNReal.ofReal C1 * (1 + ENNReal.ofReal (‖ξ‖ ^ 2)) * M1 ξ := mul_le_mul' e2 e1
    _ = G ξ := by simp only [G]; ring

include hT hν hfix hG hR0 hRb in
/-- **`∂ₜu ∈ L²`, uniformly on `[0,T)`.** -/
theorem timeSlice_physU : ∃ K : ℝ, ∀ t ∈ Ico (0 : ℝ) T, TimeSlice K (physU w) t := by
  obtain ⟨BT, hBT0, hBT⟩ := l2_bound_W1 hT hν hG hR0 hRb
  refine ⟨3 * BT, fun t ht => ?_⟩
  have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
  set g : Space → ℝ := fun x => ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)‖ ^ 2
  have hgi : Integrable g := integrable_space_euclid (g := fun y => ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) y‖ ^ 2) (integrable_finsetSum _ fun k _ => (hBT k t htI).1)
  have hgv : ∫ x, g x ≤ 3 * BT := by
    rw [integral_space_euclid (fun y => ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) y‖ ^ 2),
      integral_finsetSum _ fun k _ => (hBT k t htI).1]
    calc ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) y‖ ^ 2 ≤ ∑ _k : Fin 3, BT :=
          Finset.sum_le_sum fun k _ => (hBT k t htI).2
      _ = 3 * BT := by simp
  have hF := fun x => timeDerivative_physU_eq hT hν a hfix hG ht.1 ht.2 x
  have hc : Continuous (fun x => timeDerivative (physU w) t x) := by
    have : (fun x => timeDerivative (physU w) t x) = fun x k =>
        -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)).re :=
      funext hF
    rw [this]
    exact continuous_pi fun k => continuous_const.mul (Complex.continuous_re.comp
      ((continuous_fourierInv (integrable_of_hmom
        (fun α => integrable_moment hT hν hG 1 α htI k))).comp (PiLp.continuous_toLp 2 _)))
  have hb : ∀ x, ‖timeDerivative (physU w) t x‖ ^ 2 ≤ g x := by
    intro x
    refine (sq_norm_le_sum _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [hF x]
    have hπ : 0 < Real.pi := Real.pi_pos
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
    refine (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)).trans ?_
    have : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    calc 1 / (2 * Real.pi) * ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)‖
        ≤ 1 * ‖𝓕⁻ (fun ξ => W ν w 1 t ξ k) (euclidPoint x)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  have hI : Integrable (fun x : Space => ‖timeDerivative (physU w) t x‖ ^ 2) :=
    hgi.mono' ((continuous_norm.comp hc).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb x)
  exact ⟨hI, (integral_mono hI hgi hb).trans hgv⟩

include hT hν hfix hG hR0 hRb in
/-- **The Wiener pair is in `R`.** -/
theorem regularOnCompacts_phys : RegularOnCompacts T (physU w) (physP w) := by
  obtain ⟨K1, hK1⟩ := regSlice_physU hT hν hG hR0 hRb
  obtain ⟨K2, hK2⟩ := presSlice_physP hT hν hG hR0 hRb
  obtain ⟨K3, hK3⟩ := timeSlice_physU hT hν a hfix hG hR0 hRb
  intro T' hT'
  refine ⟨max K1 (max K2 K3), fun t ht => ⟨?_, ?_, ?_⟩⟩
  · exact (hK1 t ⟨ht.1, ht.2.trans hT'.le⟩).mono (le_max_left _ _)
  · exact (hK2 t ⟨ht.1, ht.2.trans hT'.le⟩).mono
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hK3 t ⟨ht.1, lt_of_le_of_lt ht.2 hT'⟩).mono
      ((le_max_right _ _).trans (le_max_right _ _))

end Full

open Navier.Analysis.ContinuousLeiLinPhysicalCarrier Navier.Analysis.WienerSchwartzLocal
  Navier.Analysis.WienerLocalExistence
open Navier.Analysis.FourierMajorant (euclidComponent) in
/-- **Local classical existence at every positive viscosity, landing in `R`.** -/
theorem localClassicalExistenceIn_R :
    Navier.Analysis.ClassDecomposition.LocalClassicalExistenceIn
      Navier.Analysis.ClassDecomposition.RegularOnCompacts := by
  intro νp hνp u₀ hdiv
  set v₀ : SchwartzVelocity := (-(2 * Real.pi)) • u₀ with hv₀
  set ν : ℝ := 4 * Real.pi ^ 2 * νp with hνdef
  have hν : 0 < ν := by positivity
  set a₀ : V1 := wienerDatum v₀ with ha₀def
  set n : ℝ := ‖a₀‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set T : ℝ := ν / (10 ^ 6 * (n + 1)) with hTdef
  have hT : 0 < T := by positivity
  have hsmall6 : 10 ^ 6 * T * ‖a₀‖ ^ 2 ≤ ν := by
    rw [← hn, hTdef]
    rw [show 10 ^ 6 * (ν / (10 ^ 6 * (n + 1))) * n = ν * (n / (n + 1)) by field_simp]
    have : n / (n + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have hsmall4 : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν := by
    have : 0 ≤ T * ‖a₀‖ ^ 2 := by positivity
    nlinarith
  obtain ⟨x, hxle, hxeq, w, hxw, hfix, hG, hsm, hreal, hsym⟩ :=
    Navier.Analysis.WienerReality.exists_real_smooth_wienerSolution hν hT v₀ hsmall4
  set a : ES → ComplexSpace := fourierDatum v₀ with hadef
  -- the datum is bounded
  set A : ℝ := ∑ i : Fin 3,
    ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ with hAdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => norm_nonneg _
  have haA : ∀ ξ (i : Fin 3), ‖a ξ i‖ ≤ A := by
    intro ξ i
    have h1 : ‖a ξ i‖ ≤
        ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ :=
      ((𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction.norm_coe_le_norm
        ξ)
    exact h1.trans (Finset.single_le_sum (f := fun i =>
      ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i))
  have ha₀ : ∀ i, a₀ i ∈ Navier.Analysis.WienerLinfBound.Zb A := by
    intro i
    show ∀ᵐ ξ ∂(volume : Measure ES), ‖(a₀ i) ξ‖ ≤ A
    filter_upwards [coeFn_wienerDatum v₀ i] with ξ h
    rw [h]; exact haA ξ i
  have hxS := Navier.Analysis.WienerLinfBound.fixedPoint_mem_linfSet hν hT a₀ hsmall6 hA ha₀ x
    hxle hxeq
  have hRb := Navier.Analysis.WienerEnergy.ae_uniform_bound hT hν a hfix x hG.1 hxw hA
    (by positivity) hxS hxle (Eventually.of_forall fun ξ i => haA ξ i)
  set Rt : ℝ := A + 27 * (2 * A) * (2 * ‖a₀‖) * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt T) with hRt
  have hR0 : 0 ≤ Rt := by positivity
  have ha : Navier.Analysis.ContinuousLeiLinReality.ProfileDivergenceFree a :=
    profileDivergenceFree_fourierDatum v₀ (divergenceFreeInitial_smul _ hdiv)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hw0 : ∀ ξ, w 0 ξ = a ξ := fun ξ => by
    rw [hfix 0 ⟨le_rfl, hT.le⟩ ξ, mild_zero]
  have hinit : ∀ x : Space, physU w 0 x = u₀ x := by
    intro x
    funext i
    have hw0i : (fun ξ => w 0 ξ i) = fun ξ => a ξ i := by
      funext ξ; rw [hw0]
    have h := physicalCoord_fourierDatum v₀ i (euclidPoint x)
    unfold physicalCoord at h
    show -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => w 0 ξ i) (euclidPoint x)).re = u₀ x i
    rw [hw0i, h, Complex.ofReal_re]
    show -(1 / (2 * Real.pi)) * ((-(2 * Real.pi)) • u₀) x i = u₀ x i
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  -- per-slice facts
  have hwint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => w t ξ k) :=
    fun t ht k => integrable_of_hmom (hmom_w hT hν hG ht k)
  have hwm : ∀ t (k : Fin 3), StronglyMeasurable (fun ξ => w t ξ k) :=
    fun t k => (continuous_apply k).comp_stronglyMeasurable (hG.1 t)
  have hwb : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES), ‖w t ξ k‖ ≤ Rt := by
    intro t ht k
    filter_upwards [hRb] with ξ h using (norm_le_pi_norm _ k).trans (h t ht)
  have hLw : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 ≠ ⊤ :=
    fun t ht k => lintegral_sq_ne_top (hwint t ht k) (hwb t ht k)
  have hPl : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      ∫⁻ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 :=
    fun t ht k => Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le (hwm t k)
      (hwint t ht k)
  have hUc : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Continuous (𝓕⁻ (fun ξ => w t ξ k)) :=
    fun t ht k => Navier.Analysis.WienerSmoothPath.continuous_fourierInv (hwint t ht k)
  have hUint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      Integrable (fun y => ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral (hUc t ht k)
      (ne_top_of_le_ne_top (hLw t ht k) (hPl t ht k))
  have hwsq : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => ‖w t ξ k‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral' (hwm t k).aestronglyMeasurable (hLw t ht k)
  set c : ℝ := 1 / (2 * Real.pi) with hc
  have hbound : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x : Space =>
      c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2) := fun t ht =>
    integrable_space_euclid (g := fun y => c ^ 2 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2)
      ((integrable_finsetSum _ fun k _ => hUint t ht k).const_mul _)
  refine ⟨T, hT, physU w, physP w, hinit, ⟨⟨smoothVelocityBefore_physU hsm,
    Navier.Analysis.WienerPressureSmooth.smoothPressureBefore_physP hT hν a hfix hG,
    incompressibleBefore_physU hT hν a hfix hG ha,
    satisfiesNavierStokesBefore_physU_visc hT hν a hfix hG rfl ha hreal⟩, ?_, ?_⟩,
    regularOnCompacts_phys hT hν a hfix hG hR0 hRb⟩
  · -- finite energy
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hcont : Continuous (fun x : Space => physU w t x) := by
      refine continuous_pi fun k => ?_
      exact continuous_const.mul (Complex.continuous_re.comp ((hUc t ht k).comp
        (PiLp.continuous_toLp 2 _)))
    refine (hbound t ht).mono' ((continuous_norm.comp hcont).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (sq_norm_le_sum _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => physU_sq_le w t x k
  · -- energy inequality
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hKt : kineticEnergy (physU w) t =
        c ^ 2 * ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 := by
      unfold kineticEnergy
      have hpt : ∀ x : Space, ∑ i : Fin 3, (physU w t x i) ^ 2 =
          c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2 := by
        intro x
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => physU_sq_eq w t x k ?_
        exact Complex.conj_eq_iff_im.mp (hreal t ht k (euclidPoint x))
      simp_rw [hpt]
      rw [integral_space_euclid (fun y => c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2),
        integral_const_mul, integral_finsetSum _ fun k _ => hUint t ht k]
    have hK0 : kineticEnergy (physU w) 0 = ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      unfold kineticEnergy
      simp_rw [hinit]
    have hEW : ∀ s ∈ Icc (0 : ℝ) T, Navier.Analysis.WienerEnergy.EW w s =
        ∑ k : Fin 3, ∫ ξ, ‖w s ξ k‖ ^ 2 := by
      intro s hs
      unfold Navier.Analysis.WienerEnergy.EW Navier.Analysis.WienerEnergy.eW
      exact integral_finsetSum _ fun k _ => hwsq s hs k
    have hE := Navier.Analysis.WienerEnergy.energy_antitone hT hν a hfix hG hR0 hRb hsym ha ht
    rw [hEW t ht, hEW 0 ⟨le_rfl, hT.le⟩] at hE
    have hdat : ∑ k : Fin 3, ∫ ξ, ‖w 0 ξ k‖ ^ 2 =
        (2 * Real.pi) ^ 2 * ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      simp_rw [hw0]
      rw [hadef, fourierDatum_energy_eq_physical v₀, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hv₀, smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hle : ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 ≤
        ∑ k : Fin 3, ∫ ξ, ‖w t ξ k‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => integral_sq_le_of_lintegral (hUint t ht k) (hwsq t ht k)
        (hPl t ht k)
    rw [hKt, hK0]
    have hc2 : c ^ 2 * (2 * Real.pi) ^ 2 = 1 := by rw [hc]; field_simp
    calc c ^ 2 * ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2
        ≤ c ^ 2 * ∑ k : Fin 3, ∫ ξ, ‖w 0 ξ k‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (hle.trans hE) (by positivity)
      _ = ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
          rw [hdat, ← mul_assoc, hc2, one_mul]


/-- The primary R-route crown reduction: local existence is discharged in `R`. -/
theorem wholeSpaceGlobalRegularity_of_R_leaves (N : CriticalQuantity)
    (hcont : Navier.Analysis.ClassDecomposition.DatumContinuationIn
      Navier.Analysis.ClassDecomposition.RegularOnCompacts N)
    (hapriori : Navier.Analysis.ClassDecomposition.APrioriIn
      Navier.Analysis.ClassDecomposition.RegularOnCompacts N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  Navier.Analysis.ClassDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_R
    N localClassicalExistenceIn_R hcont hapriori

end Navier.Analysis.WienerRegularityFull

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRegularityFull.localClassicalExistenceIn_R
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRegularityFull.wholeSpaceGlobalRegularity_of_R_leaves
