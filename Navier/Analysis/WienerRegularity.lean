import Navier.Analysis.WienerLocalClassical
import Navier.Analysis.ClassDecomposition

/-!
# The Wiener solution lies in the regular class `R`

First and second spatial derivatives of `physU w` are inverse transforms of
`ξ^α w`; the Plancherel inequality, the uniform essential bound `‖w‖ ≤ R` and
the time-uniform majorant moments give `L²` bounds uniform on `[0,T]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate

namespace Navier.Analysis.WienerRegularity

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
open Navier.Analysis.CriticalControlDecomposition (CriticalQuantity)

section Reg

variable {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
  {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w) {R : ℝ} (hR0 : 0 ≤ R)
  (hRb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖w t ξ‖ ≤ R)

include hT hν hG hR0 hRb in
/-- **Uniform `L²` bound for the inverse transform of `ξ^α wₖ`.** -/
theorem l2_bound :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ (α : Fin 3 → ℕ) (k : Fin 3) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      Integrable (fun y => ‖𝓕⁻ (fun ξ => mono α ξ * w t ξ k) y‖ ^ 2) ∧
      (∫ y, ‖𝓕⁻ (fun ξ => mono α ξ * w t ξ k) y‖ ^ 2) ≤ B (2 * deg α) := by
  have hGc := hG
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hGc
  refine ⟨fun n => (ENNReal.ofReal R * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * M ξ).toReal,
    fun n => ENNReal.toReal_nonneg, fun α k t ht => ?_⟩
  set f : ES → ℂ := fun ξ => mono α ξ * w t ξ k with hf
  have hfm : StronglyMeasurable f :=
    ((by unfold mono; fun_prop : Continuous (mono α)).stronglyMeasurable).mul
      ((continuous_apply k).comp_stronglyMeasurable (hm t))
  have hfi : Integrable f := hmom_w hT hν hG ht k α
  have hbd : ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal R * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * M ξ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hb, hRb] with ξ h1 h2
    have e1 : ‖w t ξ k‖ₑ ≤ ENNReal.ofReal R := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal ((norm_le_pi_norm _ k).trans (h2 t ht))
    have e2 : ‖w t ξ k‖ₑ ≤ M ξ := (enorm_coord_le _ k).trans (h1 t ht)
    have e3 : ‖mono α ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [pow_mul, ← pow_mul, mul_comm 2 (deg α), pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_mono_le α ξ) 2
    calc ‖f ξ‖ₑ ^ 2 = ‖mono α ξ‖ₑ ^ 2 * (‖w t ξ k‖ₑ * ‖w t ξ k‖ₑ) := by
          rw [hf]; simp only [enorm_mul]; ring
      _ ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * (ENNReal.ofReal R * M ξ) :=
          mul_le_mul' e3 (mul_le_mul' e1 e2)
      _ = ENNReal.ofReal R * (ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * M ξ) := by ring
  have hfin : ENNReal.ofReal R * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * deg α)) * M ξ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmom _)
  have hPl := (Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le hfm hfi).trans hbd
  have hint := integrable_norm_sq_of_lintegral (continuous_fourierInv hfi)
    (ne_top_of_le_ne_top hfin hPl)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_mono hfin (le_trans (le_of_eq (lintegral_congr fun y => ?_)) hPl)
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

include hT hν hG in
theorem fderiv_physU_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    (fun x => fderiv ℝ (physU w t) x (basisVector i)) = fun x k =>
      -(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ => mono (ej i) ξ * w t ξ k) (euclidPoint x)).re := by
  funext x k
  rw [fderiv_physU_apply hT hν hG ht, euclidPoint_basisVector,
    fderiv_fourierInv_single (integrable_of_hmom (hmom_w hT hν hG ht k))
      (integrable_coord_mul (hmom_w hT hν hG ht k)) _ i]
  rw [show (fun ξ : ES => ((ξ i : ℝ) : ℂ) * w t ξ k) = fun ξ => mono (ej i) ξ * w t ξ k from
    funext fun ξ => by rw [mono_ej]]

include hT hν hG in
theorem fderiv2_physU_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i j : Fin 3) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ (physU w t) y (basisVector i)) x (basisVector j)) =
      fun x k => -(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I *
        ((2 * Real.pi : ℂ) * Complex.I *
          𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) (euclidPoint x))).re := by
  funext x k
  rw [fderiv_physU_fun hT hν hG ht i]
  rw [fderiv_reCompVec_apply (F := fun k z =>
      fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) z (EuclideanSpace.single i 1))
    (fun k y => differentiable_fderiv_fourierInv (hmom_w hT hν hG ht k) i y),
    euclidPoint_basisVector, fderiv_fderiv_fourierInv_single (hmom_w hT hν hG ht k) j i]
  rw [show (fun ξ : ES => ((ξ j : ℝ) : ℂ) * (((ξ i : ℝ) : ℂ) * w t ξ k)) =
      fun ξ => mono (ej i + ej j) ξ * w t ξ k from
    funext fun ξ => by rw [mono_ej_ej]; ring]


theorem mono_add (α β : Fin 3 → ℕ) (ξ : ES) : mono (α + β) ξ = mono α ξ * mono β ξ := by
  unfold mono
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]

include hT hν hG in
theorem fderiv3_physU_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i j l : Fin 3) :
    (fun x => fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ (physU w t) y (basisVector i)) z
      (basisVector j)) x (basisVector l)) =
      fun x k => -(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I *
        ((2 * Real.pi : ℂ) * Complex.I * ((2 * Real.pi : ℂ) * Complex.I *
          𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) (euclidPoint x)))).re := by
  have hg : ∀ k : Fin 3, ∀ α : Fin 3 → ℕ,
      Integrable (fun ξ => mono α ξ * (mono (ej i + ej j) ξ * w t ξ k)) := by
    intro k α
    refine (hmom_w hT hν hG ht k (α + (ej i + ej j))).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only [mono_add]; ring
  have hF2 := fderiv2_physU_eq hT hν hG ht i j
  funext x k
  rw [hF2]
  set F : Fin 3 → ES → ℂ := fun k z => (2 * Real.pi : ℂ) * Complex.I *
    ((2 * Real.pi : ℂ) * Complex.I * 𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) z) with hFdef
  have hFd : ∀ k y, DifferentiableAt ℝ (F k) y := fun k y =>
    ((differentiable_fourierInv (hg k) y).const_mul _).const_mul _
  have h := fderiv_reCompVec_apply hFd (-(1 / (2 * Real.pi))) x (basisVector l) k
  simp only [hFdef] at h
  rw [h, euclidPoint_basisVector]
  rw [fderiv_const_mul ((differentiable_fourierInv (hg k) _).const_mul _),
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_const_mul (differentiable_fourierInv (hg k) _),
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_fourierInv_single (integrable_of_hmom (hg k)) (integrable_coord_mul (hg k)) _ l]
  rw [show (fun ξ : ES => ((ξ l : ℝ) : ℂ) * (mono (ej i + ej j) ξ * w t ξ k)) =
      fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k from
    funext fun ξ => by rw [mono_add_ej (ej i + ej j) l]; ring]

theorem abs_re_scaled_le (z : ℂ) :
    |-(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I * z).re| ≤ ‖z‖ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
  refine (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)).trans
    (le_of_eq ?_)
  have h2 : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2]
  field_simp

include hT hν hG hR0 hRb in
/-- **The Wiener velocity is regular on compacts.** -/
theorem regSlice_physU :
    ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T, Navier.Analysis.ClassDecomposition.RegSlice K (physU w t) := by
  obtain ⟨B, hB0, hB⟩ := l2_bound hT hν hG hR0 hRb
  set c2 : ℝ := (2 * Real.pi) ^ 2
  set c4 : ℝ := (2 * Real.pi) ^ 4
  set K : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    (3 * B (2 * deg (ej i)) + c2 * (3 * B (2 * deg (ej i + ej j))) +
      c4 * (3 * B (2 * deg (ej i + ej j + ej l)))) with hK
  refine ⟨K, fun t htT i j l => ?_⟩
  have hnn : ∀ i j l : Fin 3, 0 ≤ 3 * B (2 * deg (ej i)) + c2 * (3 * B (2 * deg (ej i + ej j))) +
      c4 * (3 * B (2 * deg (ej i + ej j + ej l))) := fun i j l => by
    have := hB0 (2 * deg (ej i)); have := hB0 (2 * deg (ej i + ej j))
    have := hB0 (2 * deg (ej i + ej j + ej l)); positivity
  have hterm_le : 3 * B (2 * deg (ej i)) + c2 * (3 * B (2 * deg (ej i + ej j))) +
      c4 * (3 * B (2 * deg (ej i + ej j + ej l))) ≤ K := by
    calc _ ≤ ∑ l' : Fin 3, (3 * B (2 * deg (ej i)) + c2 * (3 * B (2 * deg (ej i + ej j))) +
            c4 * (3 * B (2 * deg (ej i + ej j + ej l')))) :=
          Finset.single_le_sum (f := fun l' => 3 * B (2 * deg (ej i)) +
            c2 * (3 * B (2 * deg (ej i + ej j))) + c4 * (3 * B (2 * deg (ej i + ej j + ej l'))))
            (fun l' _ => hnn i j l') (Finset.mem_univ l)
      _ ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, (3 * B (2 * deg (ej i)) +
            c2 * (3 * B (2 * deg (ej i + ej j'))) + c4 * (3 * B (2 * deg (ej i + ej j' + ej l')))) :=
          Finset.single_le_sum (f := fun j' => ∑ l' : Fin 3, (3 * B (2 * deg (ej i)) +
            c2 * (3 * B (2 * deg (ej i + ej j'))) + c4 * (3 * B (2 * deg (ej i + ej j' + ej l')))))
            (fun j' _ => Finset.sum_nonneg fun l' _ => hnn i j' l') (Finset.mem_univ j)
      _ ≤ K := Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ∑ l' : Fin 3,
            (3 * B (2 * deg (ej i')) + c2 * (3 * B (2 * deg (ej i' + ej j'))) +
              c4 * (3 * B (2 * deg (ej i' + ej j' + ej l')))))
            (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun l' _ => hnn i' j' l')
            (Finset.mem_univ i)
  have hc4 : 0 ≤ c4 := by positivity
  have hBijl := hB0 (2 * deg (ej i + ej j + ej l))
  have hc2 : 0 ≤ c2 := by positivity
  have hBi := hB0 (2 * deg (ej i)); have hBij := hB0 (2 * deg (ej i + ej j))
  -- first derivatives
  set g1 : Space → ℝ := fun x => ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i) ξ * w t ξ k) (euclidPoint x)‖ ^ 2 with hg1
  have hg1i : Integrable g1 := integrable_space_euclid (g := fun y => ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i) ξ * w t ξ k) y‖ ^ 2)
    (integrable_finsetSum _ fun k _ => (hB (ej i) k t htT).1)
  have hg1v : ∫ x, g1 x ≤ 3 * B (2 * deg (ej i)) := by
    rw [hg1, integral_space_euclid (fun y => ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => mono (ej i) ξ * w t ξ k) y‖ ^ 2),
      integral_finsetSum _ fun k _ => (hB (ej i) k t htT).1]
    calc ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => mono (ej i) ξ * w t ξ k) y‖ ^ 2
        ≤ ∑ _k : Fin 3, B (2 * deg (ej i)) := Finset.sum_le_sum fun k _ => (hB (ej i) k t htT).2
      _ = 3 * B (2 * deg (ej i)) := by simp
  have hF1 := fderiv_physU_eq hT hν hG htT i
  have hc1 : Continuous (fun x => fderiv ℝ (physU w t) x (basisVector i)) := by
    rw [hF1]
    refine continuous_pi fun k => continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.mul ((continuous_fourierInv ?_).comp (PiLp.continuous_toLp 2 _))))
    exact hmom_w hT hν hG htT k (ej i)
  have hb1 : ∀ x, ‖fderiv ℝ (physU w t) x (basisVector i)‖ ^ 2 ≤ g1 x := by
    intro x
    refine (sq_norm_le_sum _).trans (Finset.sum_le_sum fun k _ => ?_)
    have := congrFun (congrFun hF1 x) k
    rw [this, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_re_scaled_le _) 2
  have hI1 : Integrable (fun x : Space => ‖fderiv ℝ (physU w t) x (basisVector i)‖ ^ 2) :=
    hg1i.mono' ((continuous_norm.comp hc1).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb1 x)
  -- second derivatives
  set g2 : Space → ℝ := fun x => c2 * ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) (euclidPoint x)‖ ^ 2 with hg2
  have hg2i : Integrable g2 := integrable_space_euclid (g := fun y => c2 * ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) y‖ ^ 2)
    ((integrable_finsetSum _ fun k _ => (hB (ej i + ej j) k t htT).1).const_mul _)
  have hg2v : ∫ x, g2 x ≤ c2 * (3 * B (2 * deg (ej i + ej j))) := by
    rw [hg2, integral_space_euclid (fun y => c2 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) y‖ ^ 2), integral_const_mul,
      integral_finsetSum _ fun k _ => (hB (ej i + ej j) k t htT).1]
    refine mul_le_mul_of_nonneg_left ?_ hc2
    calc ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) y‖ ^ 2
        ≤ ∑ _k : Fin 3, B (2 * deg (ej i + ej j)) :=
          Finset.sum_le_sum fun k _ => (hB (ej i + ej j) k t htT).2
      _ = 3 * B (2 * deg (ej i + ej j)) := by simp
  have hF2 := fderiv2_physU_eq hT hν hG htT i j
  have hc2c : Continuous (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (physU w t) y (basisVector i)) x (basisVector j)) := by
    rw [hF2]
    refine continuous_pi fun k => continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.mul (continuous_const.mul
        ((continuous_fourierInv ?_).comp (PiLp.continuous_toLp 2 _)))))
    exact hmom_w hT hν hG htT k (ej i + ej j)
  have hb2 : ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (physU w t) y (basisVector i)) x
      (basisVector j)‖ ^ 2 ≤ g2 x := by
    intro x
    refine (sq_norm_le_sum _).trans ?_
    show _ ≤ c2 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) (euclidPoint x)‖ ^ 2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := congrFun (congrFun hF2 x) k
    rw [this, ← sq_abs]
    set z := 𝓕⁻ (fun ξ => mono (ej i + ej j) ξ * w t ξ k) (euclidPoint x)
    have hz := abs_re_scaled_le ((2 * Real.pi : ℂ) * Complex.I * z)
    have hn : ‖(2 * Real.pi : ℂ) * Complex.I * z‖ = 2 * Real.pi * ‖z‖ := by
      have h2 : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2]
    rw [hn] at hz
    calc |-(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I *
          ((2 * Real.pi : ℂ) * Complex.I * z)).re| ^ 2 ≤ (2 * Real.pi * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hz 2
      _ = c2 * ‖z‖ ^ 2 := by ring
  have hI2 : Integrable (fun x : Space =>
      ‖fderiv ℝ (fun y => fderiv ℝ (physU w t) y (basisVector i)) x (basisVector j)‖ ^ 2) :=
    hg2i.mono' ((continuous_norm.comp hc2c).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb2 x)
  -- third derivatives
  set g3 : Space → ℝ := fun x => c4 * ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) (euclidPoint x)‖ ^ 2 with hg3
  have hg3i : Integrable g3 := integrable_space_euclid (g := fun y => c4 * ∑ k : Fin 3,
    ‖𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) y‖ ^ 2)
    ((integrable_finsetSum _ fun k _ => (hB (ej i + ej j + ej l) k t htT).1).const_mul _)
  have hg3v : ∫ x, g3 x ≤ c4 * (3 * B (2 * deg (ej i + ej j + ej l))) := by
    rw [hg3, integral_space_euclid (fun y => c4 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) y‖ ^ 2), integral_const_mul,
      integral_finsetSum _ fun k _ => (hB (ej i + ej j + ej l) k t htT).1]
    refine mul_le_mul_of_nonneg_left ?_ hc4
    calc ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) y‖ ^ 2
        ≤ ∑ _k : Fin 3, B (2 * deg (ej i + ej j + ej l)) :=
          Finset.sum_le_sum fun k _ => (hB (ej i + ej j + ej l) k t htT).2
      _ = 3 * B (2 * deg (ej i + ej j + ej l)) := by simp
  have hF3 := fderiv3_physU_eq hT hν hG htT i j l
  have hc3c : Continuous (fun x => fderiv ℝ (fun z => fderiv ℝ
      (fun y => fderiv ℝ (physU w t) y (basisVector i)) z (basisVector j)) x (basisVector l)) := by
    rw [hF3]
    refine continuous_pi fun k => continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.mul (continuous_const.mul (continuous_const.mul
        ((continuous_fourierInv ?_).comp (PiLp.continuous_toLp 2 _))))))
    exact hmom_w hT hν hG htT k (ej i + ej j + ej l)
  have hb3 : ∀ x, ‖fderiv ℝ (fun z => fderiv ℝ
      (fun y => fderiv ℝ (physU w t) y (basisVector i)) z (basisVector j)) x
      (basisVector l)‖ ^ 2 ≤ g3 x := by
    intro x
    refine (sq_norm_le_sum _).trans ?_
    show _ ≤ c4 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) (euclidPoint x)‖ ^ 2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := congrFun (congrFun hF3 x) k
    rw [this, ← sq_abs]
    set z := 𝓕⁻ (fun ξ => mono (ej i + ej j + ej l) ξ * w t ξ k) (euclidPoint x)
    have h2 : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hz := abs_re_scaled_le ((2 * Real.pi : ℂ) * Complex.I *
      ((2 * Real.pi : ℂ) * Complex.I * z))
    have hn : ‖(2 * Real.pi : ℂ) * Complex.I * ((2 * Real.pi : ℂ) * Complex.I * z)‖ =
        (2 * Real.pi) ^ 2 * ‖z‖ := by
      have h2I : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_I, mul_one, h2]
      rw [norm_mul ((2 * Real.pi : ℂ) * Complex.I), norm_mul ((2 * Real.pi : ℂ) * Complex.I) z,
        h2I]; ring
    rw [hn] at hz
    calc _ ≤ ((2 * Real.pi) ^ 2 * ‖z‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz 2
      _ = c4 * ‖z‖ ^ 2 := by ring
  have hI3 : Integrable (fun x : Space => ‖fderiv ℝ (fun z => fderiv ℝ
      (fun y => fderiv ℝ (physU w t) y (basisVector i)) z (basisVector j)) x
      (basisVector l)‖ ^ 2) :=
    hg3i.mono' ((continuous_norm.comp hc3c).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb3 x)
  have e1 : 0 ≤ 3 * B (2 * deg (ej i)) := by positivity
  have e2 : 0 ≤ c2 * (3 * B (2 * deg (ej i + ej j))) := by positivity
  have e3 : 0 ≤ c4 * (3 * B (2 * deg (ej i + ej j + ej l))) := by positivity
  refine ⟨hI1, ?_, hI2, ?_, hI3, ?_⟩
  · refine (integral_mono hI1 hg1i hb1).trans (hg1v.trans (le_trans ?_ hterm_le)); linarith
  · refine (integral_mono hI2 hg2i hb2).trans (hg2v.trans (le_trans ?_ hterm_le)); linarith
  · refine (integral_mono hI3 hg3i hb3).trans (hg3v.trans (le_trans ?_ hterm_le)); linarith

end Reg

end Navier.Analysis.WienerRegularity
