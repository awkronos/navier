import Navier.Analysis.WienerPointwiseODE
import Navier.Analysis.ContinuousLeiLinFrequencyODE

/-!
# The mild map of a jointly measurable moment-bounded trajectory is `Good`

For a jointly strongly measurable frequency trajectory `v` whose slices have
every polynomial moment bounded uniformly for a.e. time in `[0,T]`, and a datum
`a` with every moment finite, the pointwise mild image
`t ↦ continuousMildImage ν hν a v (clamp t)` is a majorized continuous family
(`WienerPointwiseODE.Good`): measurable in frequency at every time, dominated by
`‖a‖ + 3 ∫_{[0,T]} ‖Bil(v s, v s)‖ ds` (every moment finite), and continuous in
time for a.e. frequency (`good_mildImage`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution

namespace Navier.Analysis.WienerMildGood

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.WienerPointwiseODE

/-! ## Joint measurability of the source -/

theorem stronglyMeasurable_source {v : ℝ → ES → ComplexSpace}
    (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i)) :
    StronglyMeasurable (fun p : ℝ × ES => continuousNavierBilinear (v p.1) (v p.1) p.2) := by
  have hconv : ∀ j i : Fin 3, StronglyMeasurable (fun p : ℝ × ES =>
      ((fun η => v p.1 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v p.1 η i)) p.2) := by
    intro j i
    have m1 : Measurable (fun q : (ℝ × ES) × ES => (q.2, q.1.1)) :=
      measurable_snd.prodMk (measurable_fst.comp measurable_fst)
    have m2 : Measurable (fun q : (ℝ × ES) × ES => (q.1.2 - q.2, q.1.1)) :=
      ((measurable_snd.comp measurable_fst).sub measurable_snd).prodMk
        (measurable_fst.comp measurable_fst)
    have hf : StronglyMeasurable (fun q : (ℝ × ES) × ES =>
        v q.1.1 q.2 j * v q.1.1 (q.1.2 - q.2) i) :=
      ((hvm j).comp_measurable m1).mul ((hvm i).comp_measurable m2)
    have heq : (fun p : ℝ × ES =>
        ((fun η => v p.1 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v p.1 η i)) p.2) =
        fun p : ℝ × ES => ∫ η, v p.1 η j * v p.1 (p.2 - η) i := by
      funext p; simp [convolution_def]
    rw [heq]
    exact hf.integral_prod_right'
  have hraw : Measurable (fun p : ℝ × ES => Complex.I • rawNavierConvection (v p.1) (v p.1) p.2) := by
    refine (measurable_pi_lambda _ fun i => ?_).const_smul Complex.I
    unfold rawNavierConvection
    refine Finset.measurable_sum _ fun j _ => ?_
    have hc : Measurable fun c : ℝ × ES => ((c.2 j : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).measurable
    exact hc.mul (hconv j i).measurable
  exact (measurable_continuousLeray.comp (measurable_snd.prodMk hraw)).stronglyMeasurable

/-! ## Measurability and bounds of the mild image -/

theorem enorm_le_sum_coord (z : ComplexSpace) : ‖z‖ₑ ≤ ∑ i : Fin 3, ‖z i‖ₑ := by
  rw [← ofReal_norm]
  have h : ‖z‖ ≤ ∑ i : Fin 3, ‖z i‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
      Finset.single_le_sum (f := fun j => ‖z j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => ofReal_norm _

theorem heatVec_eq_smul (ν t : ℝ) (a : ES → ComplexSpace) (ξ : ES) :
    heatVec ν t a ξ = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) • a ξ := by
  funext i
  rfl

theorem enorm_heatVec_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (a : ES → ComplexSpace) (ξ : ES) :
    ‖heatVec ν t a ξ‖ₑ ≤ ‖a ξ‖ₑ := by
  rw [heatVec_eq_smul, enorm_smul]
  have he : ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ENNReal.ofReal_le_one]
    have h2 : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  calc _ ≤ 1 * ‖a ξ‖ₑ := mul_le_mul' he le_rfl
    _ = _ := one_mul _

theorem measurable_heatVec (ν t : ℝ) {a : ES → ComplexSpace} (ha : Measurable a) :
    Measurable (heatVec ν t a) := by
  have h : heatVec ν t a = fun ξ => ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) • a ξ :=
    funext (heatVec_eq_smul ν t a)
  rw [h]
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_const.mul (continuous_norm.pow 2)).mul continuous_const).neg)).measurable.smul ha

section Mild

variable {ν T : ℝ} {v : ℝ → ES → ComplexSpace}
  (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i))
include hvm

theorem measurable_slice (s : ℝ) : Measurable (v s) :=
  measurable_pi_lambda _ fun i =>
    ((hvm i).comp_measurable (measurable_id.prodMk measurable_const)).measurable

theorem measurable_continuousDuhamel (t : ℝ) :
    Measurable (fun ξ => continuousDuhamel ν v v t ξ) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hS := stronglyMeasurable_source hvm
  have hf : StronglyMeasurable (fun p : ℝ × ES =>
      heatMode ν (t - p.1) (fun ζ : ES => continuousNavierSource v v p.1 ζ i) p.2) := by
    unfold heatMode continuousNavierSource
    have he : Continuous (fun p : ℝ × ES =>
        ((Real.exp (-(ν * ‖p.2‖ ^ 2 * (t - p.1))) : ℝ) : ℂ)) := by fun_prop
    exact he.stronglyMeasurable.mul ((continuous_apply i).comp_stronglyMeasurable hS)
  exact (hf.integral_prod_left' (μ := volume.restrict (Icc (0 : ℝ) t))).measurable

theorem enorm_continuousDuhamel_le {t : ℝ} (ht : 0 ≤ t) (hν : 0 ≤ ν) (ξ : ES) :
    ‖continuousDuhamel ν v v t ξ‖ₑ ≤
      3 * ∫⁻ s in Icc (0 : ℝ) t, ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ := by
  refine (enorm_le_sum_coord _).trans ?_
  have hc : ∀ i : Fin 3, ‖continuousDuhamel ν v v t ξ i‖ₑ ≤
      ∫⁻ s in Icc (0 : ℝ) t, ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ := by
    intro i
    unfold continuousDuhamel
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
    unfold heatMode continuousNavierSource
    rw [enorm_mul]
    have he : ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) : ℝ) : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rw [ENNReal.ofReal_le_one]
      have h1 : 0 ≤ t - s := by linarith [hs.2]
      have h2 : 0 ≤ ν * ‖ξ‖ ^ 2 * (t - s) := by positivity
      exact Real.exp_le_one_iff.mpr (by linarith)
    calc ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) : ℝ) : ℂ)‖ₑ *
          ‖continuousNavierBilinear (v s) (v s) ξ i‖ₑ
        ≤ 1 * ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ :=
          mul_le_mul' he (enorm_coord_le _ i)
      _ = _ := one_mul _
  calc ∑ i : Fin 3, ‖continuousDuhamel ν v v t ξ i‖ₑ
      ≤ ∑ _i : Fin 3, ∫⁻ s in Icc (0 : ℝ) t, ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ :=
        Finset.sum_le_sum fun i _ => hc i
    _ = _ := by simp

end Mild

/-! ## The mild image is a majorized continuous family -/

/-- Weighted moment of the source at one time, from the trajectory moments. -/
theorem lintegral_weight_source_le {v : ℝ → ES → ComplexSpace}
    (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i)) (n : ℕ) (s : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ ≤
      9 * (2 ^ (n + 1) * ((∫⁻ η, ENNReal.ofReal (‖η‖ ^ (n + 1)) * ‖v s η‖ₑ) *
        (∫⁻ η, ‖v s η‖ₑ)) + 2 ^ (n + 1) * ((∫⁻ η, ‖v s η‖ₑ) *
        ∫⁻ η, ENNReal.ofReal (‖η‖ ^ (n + 1)) * ‖v s η‖ₑ)) := by
  have hA : Measurable fun η => ‖v s η‖ₑ := (measurable_slice hvm s).enorm
  have h := lintegral_weight_convE_le (n + 1) (fun η => ‖v s η‖ₑ) (fun η => ‖v s η‖ₑ) hA hA
  refine le_trans ?_ (mul_le_mul' le_rfl h)
  have hm : Measurable fun ξ : ES =>
      ENNReal.ofReal (‖ξ‖ ^ (n + 1)) * ∫⁻ η, ‖v s η‖ₑ * ‖v s (ξ - η)‖ₑ :=
    (ENNReal.measurable_ofReal.comp (continuous_norm.pow (n + 1)).measurable).mul
      (measurable_convMaj hA hA)
  rw [← lintegral_const_mul _ hm]
  refine lintegral_mono fun ξ => ?_
  calc ENNReal.ofReal (‖ξ‖ ^ n) * ‖continuousNavierBilinear (v s) (v s) ξ‖ₑ
      ≤ ENNReal.ofReal (‖ξ‖ ^ n) * (9 * ‖ξ‖ₑ * convE (v s) (v s) ξ) :=
        mul_le_mul' le_rfl (enorm_bilinear_le _ _ ξ)
    _ = 9 * (ENNReal.ofReal (‖ξ‖ ^ (n + 1)) * ∫⁻ η, ‖v s η‖ₑ * ‖v s (ξ - η)‖ₑ) := by
        rw [← ofReal_pow_mul_enorm]; unfold convE; ring

open Navier.Analysis.ContinuousLeiLinFrequencyODE in
/-- **The mild image of a jointly measurable, moment-bounded trajectory is a
majorized continuous family on `[0,T]`.** -/
theorem good_mildImage {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) {a : ES → ComplexSpace}
    (ham : Measurable a) (hamom : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ ≠ ⊤)
    {v : ℝ → ES → ComplexSpace}
    (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i))
    (hvmom : ∀ n : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖v s ξ‖ₑ ≤ C) :
    Good T (fun t => continuousMildImage ν hν a v (projIcc 0 T hT.le t)) := by
  set Sb : ℝ × ES → ℝ≥0∞ := fun p => ‖continuousNavierBilinear (v p.1) (v p.1) p.2‖ₑ with hSbd
  have hSb : Measurable Sb := (stronglyMeasurable_source hvm).measurable.enorm
  set μs : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hμs
  set I : ES → ℝ≥0∞ := fun ξ => ∫⁻ s, Sb (s, ξ) ∂μs with hId
  have hI : Measurable I := hSb.lintegral_prod_left'
  have hw : ∀ n : ℕ, Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) :=
    fun n => ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable
  -- moments of I
  have hImom : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * I ξ ≠ ⊤ := by
    intro n
    obtain ⟨C1, hC1, hv1⟩ := hvmom (n + 1)
    obtain ⟨C0, hC0, hv0⟩ := hvmom 0
    set K : ℝ≥0∞ := 9 * (2 ^ (n + 1) * (C1 * C0) + 2 ^ (n + 1) * (C0 * C1)) with hK
    have hKfin : K ≠ ⊤ := by
      rw [hK]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hC1 hC0),
          ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hC0 hC1)⟩)
    have hswap : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * I ξ =
        ∫⁻ s, (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * Sb (s, ξ)) ∂μs := by
      have hF : Measurable (Function.uncurry fun (ξ : ES) (s : ℝ) =>
          ENNReal.ofReal (‖ξ‖ ^ n) * Sb (s, ξ)) :=
        ((hw n).comp measurable_fst).mul (hSb.comp measurable_swap)
      have hI' : ∀ ξ : ES, ENNReal.ofReal (‖ξ‖ ^ n) * I ξ =
          ∫⁻ s, ENNReal.ofReal (‖ξ‖ ^ n) * Sb (s, ξ) ∂μs := fun ξ => by
        have hm : Measurable fun s : ℝ => Sb (s, ξ) :=
          hSb.comp (measurable_id.prodMk measurable_const)
        exact (lintegral_const_mul _ hm).symm
      rw [lintegral_congr hI']
      exact lintegral_lintegral_swap hF.aemeasurable
    rw [hswap]
    have hbound : ∀ᵐ s ∂μs, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * Sb (s, ξ) ≤ K := by
      filter_upwards [hv1, hv0] with s h1 h0
      have h0' : ∫⁻ η, ‖v s η‖ₑ ≤ C0 := by simpa using h0
      refine (lintegral_weight_source_le hvm n s).trans ?_
      rw [hK]
      gcongr
    have hμfin : μs Set.univ ≠ ⊤ := by
      rw [hμs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hKfin hμfin) ?_
    calc ∫⁻ s, (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * Sb (s, ξ)) ∂μs ≤ ∫⁻ _s, K ∂μs :=
          lintegral_mono_ae hbound
      _ = K * μs Set.univ := lintegral_const K
  refine ⟨fun t => ?_, fun ξ => ‖a ξ‖ₑ + 3 * I ξ, ham.enorm.add (measurable_const.mul hI), ?_,
    fun n => ?_, ?_⟩
  · show StronglyMeasurable (fun ξ => heatVec ν (projIcc 0 T hT.le t) a ξ +
      continuousDuhamel ν v v (projIcc 0 T hT.le t) ξ)
    exact ((measurable_heatVec ν _ ham).add (measurable_continuousDuhamel hvm _)).stronglyMeasurable
  · refine Eventually.of_forall fun ξ t _ => ?_
    set t' := projIcc 0 T hT.le t
    have ht' : (t' : ℝ) ∈ Icc (0 : ℝ) T := t'.2
    show ‖heatVec ν t' a ξ + continuousDuhamel ν v v t' ξ‖ₑ ≤ ‖a ξ‖ₑ + 3 * I ξ
    refine (enorm_add_le _ _).trans (add_le_add (enorm_heatVec_le hν.le ht'.1 a ξ) ?_)
    refine (enorm_continuousDuhamel_le hvm ht'.1 hν.le ξ).trans ?_
    refine mul_le_mul' le_rfl (lintegral_mono_set (Icc_subset_Icc_right ht'.2))
  · have hsplit : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * (‖a ξ‖ₑ + 3 * I ξ) =
        (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ) +
          3 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * I ξ := by
      have h1 : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * I ξ := (hw n).mul hI
      have h2 : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ :=
        (hw n).mul ham.enorm
      rw [← lintegral_const_mul _ h1, ← lintegral_add_left h2]
      refine lintegral_congr fun ξ => ?_
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hamom n, ENNReal.mul_ne_top (by simp) (hImom n)⟩
  · have hIfin : ∀ᵐ ξ ∂(volume : Measure ES), I ξ < ⊤ :=
      ae_lt_top hI (by simpa using hImom 0)
    filter_upwards [hIfin] with ξ hξ
    have hcongr : ∀ t ∈ Icc (0 : ℝ) T, continuousMildImage ν hν a v (projIcc 0 T hT.le t) ξ =
        heatVec ν t a ξ + continuousDuhamel ν v v t ξ := fun t ht => by
      rw [projIcc_of_mem hT.le ht]; rfl
    refine ContinuousOn.congr ?_ hcongr
    refine ContinuousOn.add ?_ ?_
    · have h : (fun t => heatVec ν t a ξ) =
          fun t => ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) • a ξ :=
        funext fun t => heatVec_eq_smul ν t a ξ
      rw [h]
      exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).smul continuous_const).continuousOn
    · refine continuousOn_pi.mpr fun i => ?_
      have hSi : Integrable (fun s => continuousNavierBilinear (v s) (v s) ξ) μs := by
        refine ⟨(stronglyMeasurable_source hvm).comp_measurable
          (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable, ?_⟩
        exact hξ
      have hG : IntegrableOn (weightedSource ν v v ξ i) (uIcc 0 T) := by
        rw [uIcc_of_le hT.le]
        refine (hSi.norm.const_mul (Real.exp (ν * ‖ξ‖ ^ 2 * T))).mono' ?_ ?_
        · unfold weightedSource continuousNavierSource
          exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).aestronglyMeasurable).smul
            ((continuous_apply i).comp_aestronglyMeasurable hSi.1)
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          unfold weightedSource continuousNavierSource
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine mul_le_mul (Real.exp_le_exp.mpr ?_) (norm_le_pi_norm _ i) (norm_nonneg _)
            (Real.exp_pos _).le
          have : 0 ≤ ν * ‖ξ‖ ^ 2 := by positivity
          nlinarith [hs.2]
      have hprim := intervalIntegral.continuousOn_primitive_interval hG
      rw [uIcc_of_le hT.le] at hprim
      have hE : Continuous fun t : ℝ => ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) := by fun_prop
      refine (hE.continuousOn.mul hprim).congr fun t ht => ?_
      exact continuousDuhamel_coord_eq ν v v t ht.1 ξ i

end Navier.Analysis.WienerMildGood

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerMildGood.good_mildImage
