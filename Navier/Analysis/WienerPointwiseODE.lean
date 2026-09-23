import Navier.Analysis.WienerSmoothPath
import Navier.Analysis.WienerMoments
import Navier.Analysis.ContinuousLeiLinFrequencyODE
import Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
import Navier.Analysis.ContinuousLeiLinPhysicalCarrier

/-!
# Pointwise time regularity of a continuous mild fixed point

For a pointwise fixed point `w` of the repository's mild map on `[0, T]`, this
module builds the frequencywise time-derivative hierarchy

`W 0 = w`,  `W (k+1) t = -ν‖ξ‖² W k t + ∑_{m ≤ k} C(k,m) Bil(W m t, W (k-m) t)`

(`Bil = continuousNavierBilinear`) and proves, from moment bounds, that for
almost every frequency each `W k (·, ξ)` is continuous on `[0,T]` with
derivative `W (k+1)` on `(0,T)`, together with majorants carrying every
polynomial moment.  This is the input of the Navier–Stokes instance of
`WienerSmoothPath.SmoothFourierPath`.

This first part proves the pointwise bound on the Fourier Navier symbol.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution ContDiff FourierTransform

namespace Navier.Analysis.WienerPointwiseODE

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm

/-! ## The pointwise bound on the Fourier Navier symbol -/

theorem norm_le_complexEuclideanNorm (z : ComplexSpace) : ‖z‖ ≤ complexEuclideanNorm z :=
  (pi_norm_le_iff_of_nonneg (by unfold complexEuclideanNorm; positivity)).mpr fun i =>
    Navier.Analysis.WienerL1Carrier.norm_coord_le_complexEuclideanNorm z i

theorem complexEuclideanNorm_I_smul (z : ComplexSpace) :
    complexEuclideanNorm (Complex.I • z) = complexEuclideanNorm z := by
  unfold complexEuclideanNorm complexEuclideanPoint
  rw [WithLp.toLp_smul, norm_smul, Complex.norm_I, one_mul]

/-- The convolution integral of two vector profiles, in `ℝ≥0∞`. -/
def convE (u v : ES → ComplexSpace) (ξ : ES) : ℝ≥0∞ :=
  ∫⁻ η, ‖u η‖ₑ * ‖v (ξ - η)‖ₑ

theorem enorm_conv_coord_le (u v : ES → ComplexSpace) (j i : Fin 3) (ξ : ES) :
    ‖((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ‖ₑ ≤
      convE u v ξ := by
  refine (Navier.Analysis.WienerMoments.enorm_convolution_le _ _ ξ).trans ?_
  refine lintegral_mono fun η => ?_
  gcongr
  · rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm _ j)
  · rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm _ i)

theorem enorm_coord_le_norm (ξ : ES) (j : Fin 3) : ‖((ξ j : ℝ) : ℂ)‖ₑ ≤ ‖ξ‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le ξ j)

/-- **Pointwise bound on the Fourier Navier symbol**:
`‖Bil(u,v)(ξ)‖ ≤ 9 ‖ξ‖ ∫ ‖u(η)‖ ‖v(ξ-η)‖ dη`. -/
theorem enorm_bilinear_le (u v : ES → ComplexSpace) (ξ : ES) :
    ‖continuousNavierBilinear u v ξ‖ₑ ≤ 9 * ‖ξ‖ₑ * convE u v ξ := by
  have h1 : ‖continuousNavierBilinear u v ξ‖ ≤
      ∑ i : Fin 3, ‖rawNavierConvection u v ξ i‖ := by
    refine (norm_le_complexEuclideanNorm _).trans ?_
    unfold continuousNavierBilinear
    refine (continuousLeray_norm_le ξ _).trans ?_
    rw [complexEuclideanNorm_I_smul]
    exact euclidean_norm_le_coordinate_sum _
  have h2 : ∀ i : Fin 3, ‖rawNavierConvection u v ξ i‖ₑ ≤ 3 * ‖ξ‖ₑ * convE u v ξ := by
    intro i
    unfold rawNavierConvection
    refine (enorm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖((ξ j : ℝ) : ℂ) *
          ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ‖ₑ
        ≤ ∑ _j : Fin 3, ‖ξ‖ₑ * convE u v ξ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [enorm_mul]
          exact mul_le_mul' (enorm_coord_le_norm ξ j) (enorm_conv_coord_le u v j i ξ)
      _ = 3 * ‖ξ‖ₑ * convE u v ξ := by simp; ring
  calc ‖continuousNavierBilinear u v ξ‖ₑ ≤ ∑ i : Fin 3, ‖rawNavierConvection u v ξ i‖ₑ := by
        rw [← ofReal_norm]
        refine (ENNReal.ofReal_le_ofReal h1).trans ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
        exact le_of_eq (Finset.sum_congr rfl fun i _ => ofReal_norm _)
    _ ≤ ∑ _i : Fin 3, 3 * ‖ξ‖ₑ * convE u v ξ := Finset.sum_le_sum fun i _ => h2 i
    _ = 9 * ‖ξ‖ₑ * convE u v ξ := by simp; ring

/-! ## Measurability of the Fourier Navier symbol -/

theorem measurable_continuousLeray :
    Measurable (fun p : ES × ComplexSpace => continuousLeray p.1 p.2) := by
  have hform : (fun p : ES × ComplexSpace => continuousLeray p.1 p.2) = fun p =>
      fun i => p.2 i - ((∑ l, ((Navier.Analysis.FourierMajorant.spaceProj p.1) l : ℂ) * p.2 l) /
        (((Navier.Analysis.FourierMajorant.spaceProj p.1) ⬝ᵥ
          (Navier.Analysis.FourierMajorant.spaceProj p.1) : ℝ) : ℂ)) *
          ((Navier.Analysis.FourierMajorant.spaceProj p.1) i : ℂ) := by
    funext p i
    exact Navier.Analysis.ComplexLerayNorm.complexLeray_formula _ _ i
  rw [hform]
  have hq : Continuous (fun p : ES × ComplexSpace =>
      Navier.Analysis.FourierMajorant.spaceProj p.1) :=
    Navier.Analysis.FourierMajorant.spaceProj.continuous.comp continuous_fst
  have hc : ∀ l : Fin 3, Measurable (fun p : ES × ComplexSpace =>
      ((Navier.Analysis.FourierMajorant.spaceProj p.1) l : ℂ)) := fun l =>
    (Complex.continuous_ofReal.comp ((continuous_apply l).comp hq)).measurable
  have hz : ∀ l : Fin 3, Measurable (fun p : ES × ComplexSpace => p.2 l) := fun l =>
    (measurable_pi_apply l).comp measurable_snd
  have hden : Measurable (fun p : ES × ComplexSpace =>
      (((Navier.Analysis.FourierMajorant.spaceProj p.1) ⬝ᵥ
        (Navier.Analysis.FourierMajorant.spaceProj p.1) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Continuous.dotProduct hq hq)).measurable
  exact measurable_pi_lambda _ fun i => (hz i).sub
    (((Finset.measurable_sum _ fun l _ => (hc l).mul (hz l)).div hden).mul (hc i))

theorem stronglyMeasurable_conv_coord {u v : ES → ComplexSpace} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) (j i : Fin 3) :
    StronglyMeasurable (fun ξ =>
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ) := by
  have hf : StronglyMeasurable (fun q : ES × ES => u q.2 j * v (q.1 - q.2) i) :=
    (((continuous_apply j).comp_stronglyMeasurable hu).comp_measurable measurable_snd).mul
      (((continuous_apply i).comp_stronglyMeasurable hv).comp_measurable
        (measurable_fst.sub measurable_snd))
  have heq : (fun ξ => ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun η => v η i)) ξ) = fun ξ => ∫ η, u η j * v (ξ - η) i := by
    funext ξ; simp [convolution_def]
  rw [heq]
  exact hf.integral_prod_right'

theorem stronglyMeasurable_bilinear {u v : ES → ComplexSpace} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) : StronglyMeasurable (continuousNavierBilinear u v) := by
  have hraw : Measurable (fun ξ => Complex.I • rawNavierConvection u v ξ) := by
    refine (measurable_pi_lambda _ fun i => ?_).const_smul Complex.I
    unfold rawNavierConvection
    exact Finset.measurable_sum _ fun j _ =>
      (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).measurable.mul
        (stronglyMeasurable_conv_coord hu hv j i).measurable
  have h := measurable_continuousLeray.comp (measurable_id.prodMk hraw)
  exact h.stronglyMeasurable

/-! ## Weighted convolution of `ℝ≥0∞` majorants -/

theorem lintegral_weight_convE_le (n : ℕ) (A B : ES → ℝ≥0∞) (hA : Measurable A)
    (hB : Measurable B) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, A η * B (ξ - η) ≤
      2 ^ n * ((∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * A η) * (∫⁻ η, B η)) +
      2 ^ n * ((∫⁻ η, A η) * ∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * B η) := by
  have hw : Measurable fun η : ES => ENNReal.ofReal (‖η‖ ^ n) :=
    ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable
  have hsub : Measurable fun p : ES × ES => p.1 - p.2 := measurable_fst.sub measurable_snd
  let P : ES → ES → ℝ≥0∞ := fun ξ η =>
    (2 ^ n * (ENNReal.ofReal (‖η‖ ^ n) * A η)) * B (ξ - η)
  let Q : ES → ES → ℝ≥0∞ := fun ξ η =>
    (2 ^ n * A η) * (ENNReal.ofReal (‖ξ - η‖ ^ n) * B (ξ - η))
  have hPm : Measurable (Function.uncurry P) :=
    (measurable_const.mul ((hw.comp measurable_snd).mul (hA.comp measurable_snd))).mul
      (hB.comp hsub)
  have hQm : Measurable (Function.uncurry Q) :=
    (measurable_const.mul (hA.comp measurable_snd)).mul ((hw.comp hsub).mul (hB.comp hsub))
  have hpt : ∀ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, A η * B (ξ - η) ≤
      (∫⁻ η, P ξ η) + ∫⁻ η, Q ξ η := by
    intro ξ
    rw [← lintegral_add_left hPm.of_uncurry_left, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun η => ?_
    calc ENNReal.ofReal (‖ξ‖ ^ n) * (A η * B (ξ - η))
        ≤ (2 ^ n * ENNReal.ofReal (‖η‖ ^ n) + 2 ^ n * ENNReal.ofReal (‖ξ - η‖ ^ n)) *
            (A η * B (ξ - η)) := by
          gcongr; exact Navier.Analysis.WienerMoments.ofReal_pow_norm_le n ξ η
      _ = P ξ η + Q ξ η := by simp only [P, Q]; ring
  have hT1 : ∫⁻ ξ, ∫⁻ η, P ξ η =
      2 ^ n * ((∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * A η) * (∫⁻ η, B η)) := by
    rw [lintegral_lintegral_swap hPm.aemeasurable]
    have hin : ∀ η, ∫⁻ ξ, P ξ η = (2 ^ n * (ENNReal.ofReal (‖η‖ ^ n) * A η)) * ∫⁻ ξ, B ξ := by
      intro η
      simp only [P]
      have hBη : Measurable (fun ξ : ES => B (ξ - η)) := hB.comp (measurable_id.sub_const η)
      rw [lintegral_const_mul _ hBη]
      congr 1
      exact lintegral_sub_right_eq_self B η
    simp_rw [hin]
    have hc : Measurable fun y : ES => 2 ^ n * (ENNReal.ofReal (‖y‖ ^ n) * A y) :=
      measurable_const.mul (hw.mul hA)
    have hc' : Measurable fun y : ES => ENNReal.ofReal (‖y‖ ^ n) * A y := hw.mul hA
    rw [lintegral_mul_const _ hc, lintegral_const_mul _ hc', mul_assoc]
  have hT2 : ∫⁻ ξ, ∫⁻ η, Q ξ η =
      2 ^ n * ((∫⁻ η, A η) * ∫⁻ η, ENNReal.ofReal (‖η‖ ^ n) * B η) := by
    rw [lintegral_lintegral_swap hQm.aemeasurable]
    have hin : ∀ η, ∫⁻ ξ, Q ξ η = (2 ^ n * A η) * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * B ξ := by
      intro η
      simp only [Q]
      have hBη : Measurable (fun ξ : ES => ENNReal.ofReal (‖ξ - η‖ ^ n) * B (ξ - η)) :=
        (hw.mul hB).comp (measurable_id.sub_const η)
      rw [lintegral_const_mul _ hBη]
      congr 1
      exact lintegral_sub_right_eq_self (fun ξ => ENNReal.ofReal (‖ξ‖ ^ n) * B ξ) η
    simp_rw [hin]
    have hc : Measurable fun y : ES => 2 ^ n * A y := measurable_const.mul hA
    rw [lintegral_mul_const _ hc, lintegral_const_mul _ hA, mul_assoc]
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, A η * B (ξ - η)
      ≤ ∫⁻ ξ, ((∫⁻ η, P ξ η) + ∫⁻ η, Q ξ η) := lintegral_mono hpt
    _ = (∫⁻ ξ, ∫⁻ η, P ξ η) + ∫⁻ ξ, ∫⁻ η, Q ξ η :=
        lintegral_add_left (hPm.lintegral_prod_right') _
    _ = _ := by rw [hT1, hT2]

/-! ## Majorized continuous families -/

theorem enorm_coord_le (z : ComplexSpace) (i : Fin 3) : ‖z i‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm _ i)

/-- A frequency field on `[0,T]`: measurable at each time, dominated by a
measurable majorant with every polynomial moment finite, and continuous in time
for almost every frequency. -/
def Good (T : ℝ) (U : ℝ → ES → ComplexSpace) : Prop :=
  (∀ t, StronglyMeasurable (U t)) ∧ ∃ M : ES → ℝ≥0∞, Measurable M ∧
    (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖U t ξ‖ₑ ≤ M ξ) ∧
    (∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * M ξ ≠ ⊤) ∧
    (∀ᵐ ξ ∂(volume : Measure ES), ContinuousOn (fun t => U t ξ) (Icc (0 : ℝ) T))

theorem lintegral_ne_top_of_mom {M : ES → ℝ≥0∞} (h : ∀ n : ℕ,
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * M ξ ≠ ⊤) : ∫⁻ ξ, M ξ ≠ ⊤ := by
  simpa using h 0

/-- Along `η ↦ ξ - η`, almost-everywhere statements transfer, for every `ξ`. -/
theorem ae_sub_left {P : ES → Prop} (h : ∀ᵐ η ∂(volume : Measure ES), P η) (ξ : ES) :
    ∀ᵐ η ∂(volume : Measure ES), P (ξ - η) :=
  ((volume : Measure ES).measurePreserving_sub_left ξ).quasiMeasurePreserving.ae h

theorem continuous_leray_const (ξ : ES) : Continuous (continuousLeray ξ) := by
  unfold continuousLeray
  exact (Navier.Analysis.ComplexLerayProjection.complexLeray _).continuous_of_finiteDimensional

/-- Time continuity of one convolution coordinate, by dominated convergence. -/
theorem continuousOn_conv_coord {T : ℝ} {U V : ℝ → ES → ComplexSpace}
    (hUm : ∀ t, StronglyMeasurable (U t)) (hVm : ∀ t, StronglyMeasurable (V t))
    {MU MV : ES → ℝ≥0∞}
    (hUb : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖U t η‖ₑ ≤ MU η)
    (hVb : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖V t η‖ₑ ≤ MV η)
    (hUc : ∀ᵐ η ∂(volume : Measure ES), ContinuousOn (fun t => U t η) (Icc (0 : ℝ) T))
    (hVc : ∀ᵐ η ∂(volume : Measure ES), ContinuousOn (fun t => V t η) (Icc (0 : ℝ) T))
    {ξ : ES} (hmeas : Measurable fun η => MU η * MV (ξ - η))
    (hfin : ∫⁻ η, MU η * MV (ξ - η) ≠ ⊤) (j i : Fin 3) :
    ContinuousOn (fun t => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun η => V t η i)) ξ) (Icc (0 : ℝ) T) := by
  have hfinpt : ∀ᵐ η ∂(volume : Measure ES), MU η * MV (ξ - η) < ⊤ :=
    ae_lt_top hmeas hfin
  have hbd : Integrable (fun η => (MU η * MV (ξ - η)).toReal) :=
    integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  refine continuousOn_of_dominated (bound := fun η => (MU η * MV (ξ - η)).toReal)
    (fun t _ => ?_) (fun t ht => ?_) hbd ?_
  · exact ((((continuous_apply j).comp_stronglyMeasurable (hUm t)).mul
      (((continuous_apply i).comp_stronglyMeasurable (hVm t)).comp_measurable
        (measurable_const.sub measurable_id)))).aestronglyMeasurable
  · filter_upwards [hUb, ae_sub_left hVb ξ, hfinpt] with η h1 h2 h3
    have hx : ‖U t η j * V t (ξ - η) i‖ₑ ≤ MU η * MV (ξ - η) := by
      rw [enorm_mul]
      exact mul_le_mul' ((enorm_coord_le _ j).trans (h1 t ht))
        ((enorm_coord_le _ i).trans (h2 t ht))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono h3.ne hx
  · filter_upwards [hUc, ae_sub_left hVc ξ] with η h1 h2
    exact ((continuous_apply j).comp_continuousOn h1).mul
      ((continuous_apply i).comp_continuousOn h2)

theorem ofReal_pow_mul_enorm (n : ℕ) (ξ : ES) :
    ENNReal.ofReal (‖ξ‖ ^ n) * ‖ξ‖ₑ = ENNReal.ofReal (‖ξ‖ ^ (n + 1)) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), pow_succ]

theorem measurable_convMaj {MU MV : ES → ℝ≥0∞} (hU : Measurable MU) (hV : Measurable MV) :
    Measurable fun ξ : ES => ∫⁻ η, MU η * MV (ξ - η) := by
  have h : Measurable (fun p : ES × ES => MU p.2 * MV (p.1 - p.2)) :=
    (hU.comp measurable_snd).mul (hV.comp (measurable_fst.sub measurable_snd))
  exact h.lintegral_prod_right'

theorem ae_convMaj_ne_top {MU MV : ES → ℝ≥0∞} (hU : Measurable MU) (hV : Measurable MV)
    (hUf : ∫⁻ ξ, MU ξ ≠ ⊤) (hVf : ∫⁻ ξ, MV ξ ≠ ⊤) :
    ∀ᵐ ξ ∂(volume : Measure ES), ∫⁻ η, MU η * MV (ξ - η) ≠ ⊤ := by
  have h := lintegral_weight_convE_le 0 MU MV hU hV
  simp only [pow_zero, ENNReal.ofReal_one, one_mul] at h
  have hfin : ∫⁻ ξ, ∫⁻ η, MU η * MV (ξ - η) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ h
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hUf hVf, ENNReal.mul_ne_top hUf hVf⟩
  filter_upwards [ae_lt_top (measurable_convMaj hU hV) hfin] with ξ h using h.ne

/-- **Majorized continuous families are closed under the Fourier Navier symbol.** -/
theorem good_bil {T : ℝ} {U V : ℝ → ES → ComplexSpace} (hU : Good T U) (hV : Good T V) :
    Good T (fun t => continuousNavierBilinear (U t) (V t)) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, hUc⟩ := hU
  obtain ⟨hVm, MV, hMV, hVb, hVmom, hVc⟩ := hV
  refine ⟨fun t => stronglyMeasurable_bilinear (hUm t) (hVm t),
    fun ξ => 9 * ‖ξ‖ₑ * ∫⁻ η, MU η * MV (ξ - η), ?_, ?_, ?_, ?_⟩
  · exact (measurable_const.mul measurable_enorm).mul (measurable_convMaj hMU hMV)
  · refine Eventually.of_forall fun ξ t ht => (enorm_bilinear_le _ _ ξ).trans ?_
    refine mul_le_mul' le_rfl ?_
    unfold convE
    refine lintegral_mono_ae ?_
    filter_upwards [hUb, ae_sub_left hVb ξ] with η h1 h2
    exact mul_le_mul' (h1 t ht) (h2 t ht)
  · intro n
    have h := lintegral_weight_convE_le (n + 1) MU MV hMU hMV
    have heq : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * (9 * ‖ξ‖ₑ * ∫⁻ η, MU η * MV (ξ - η)) =
        9 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (n + 1)) * ∫⁻ η, MU η * MV (ξ - η) := by
      have hmm : Measurable fun ξ : ES =>
          ENNReal.ofReal (‖ξ‖ ^ (n + 1)) * ∫⁻ η, MU η * MV (ξ - η) :=
        (ENNReal.measurable_ofReal.comp (continuous_norm.pow (n + 1)).measurable).mul
          (measurable_convMaj hMU hMV)
      rw [← lintegral_const_mul _ hmm]
      refine lintegral_congr fun ξ => ?_
      rw [← ofReal_pow_mul_enorm]
      ring
    rw [heq]
    refine ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top ?_ h)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (hUmom _) (lintegral_ne_top_of_mom hVmom)),
      ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (lintegral_ne_top_of_mom hUmom)
        (hVmom _))⟩
  · filter_upwards [ae_convMaj_ne_top hMU hMV (lintegral_ne_top_of_mom hUmom)
      (lintegral_ne_top_of_mom hVmom)] with ξ hξ
    have hc : ∀ j i : Fin 3, ContinuousOn (fun t => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ,
        volume] (fun η => V t η i)) ξ) (Icc (0 : ℝ) T) := fun j i =>
      continuousOn_conv_coord hUm hVm hUb hVb hUc hVc
        ((hMU.comp measurable_id).mul (hMV.comp (measurable_const.sub measurable_id))) hξ j i
    have hraw : ContinuousOn (fun t => Complex.I • rawNavierConvection (U t) (V t) ξ)
        (Icc (0 : ℝ) T) := by
      have hr : ContinuousOn (fun t => rawNavierConvection (U t) (V t) ξ) (Icc (0 : ℝ) T) := by
        refine continuousOn_pi.mpr fun i => ?_
        unfold rawNavierConvection
        exact continuousOn_finset_sum _ fun j _ => continuousOn_const.mul (hc j i)
      exact hr.const_smul Complex.I
    exact (continuous_leray_const ξ).comp_continuousOn hraw

theorem good_zero (T : ℝ) : Good T (fun _ _ => 0) := by
  refine ⟨fun _ => stronglyMeasurable_const, fun _ => 0, measurable_const,
    Eventually.of_forall fun ξ t _ => by simp, fun n => by simp, Eventually.of_forall fun ξ =>
      continuousOn_const⟩

theorem good_add {T : ℝ} {U V : ℝ → ES → ComplexSpace} (hU : Good T U) (hV : Good T V) :
    Good T (fun t ξ => U t ξ + V t ξ) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, hUc⟩ := hU
  obtain ⟨hVm, MV, hMV, hVb, hVmom, hVc⟩ := hV
  refine ⟨fun t => (hUm t).add (hVm t), fun ξ => MU ξ + MV ξ, hMU.add hMV, ?_, fun n => ?_, ?_⟩
  · filter_upwards [hUb, hVb] with ξ h1 h2 t ht
    exact (enorm_add_le _ _).trans (add_le_add (h1 t ht) (h2 t ht))
  · have hw : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * MU ξ :=
      (ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul hMU
    simp_rw [mul_add]
    rw [lintegral_add_left hw]
    exact ENNReal.add_ne_top.mpr ⟨hUmom n, hVmom n⟩
  · filter_upwards [hUc, hVc] with ξ h1 h2 using h1.add h2

theorem good_nsmul {T : ℝ} {U : ℝ → ES → ComplexSpace} (hU : Good T U) (c : ℕ) :
    Good T (fun t ξ => c • U t ξ) := by
  induction c with
  | zero => simpa using good_zero T
  | succ c ih =>
      have h := good_add ih hU
      convert h using 3 with t ξ
      rw [succ_nsmul]

theorem good_sum {T : ℝ} {ι : Type*} (s : Finset ι) {U : ι → ℝ → ES → ComplexSpace}
    (hU : ∀ i ∈ s, Good T (U i)) : Good T (fun t ξ => ∑ i ∈ s, U i t ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero T
  | insert a s ha ih =>
      have h := good_add (hU a (Finset.mem_insert_self a s))
        (ih fun i hi => hU i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using h

/-- The heat symbol `-ν‖ξ‖²` as a complex scalar. -/
def heatSym2 (ν : ℝ) (ξ : ES) : ℂ := (((-(ν * ‖ξ‖ ^ 2)) : ℝ) : ℂ)

theorem good_heat {T ν : ℝ} (hν : 0 ≤ ν) {U : ℝ → ES → ComplexSpace} (hU : Good T U) :
    Good T (fun t ξ => heatSym2 ν ξ • U t ξ) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, hUc⟩ := hU
  have hmeasS : Measurable (heatSym2 ν) := by
    unfold heatSym2
    exact Complex.continuous_ofReal.measurable.comp
      ((continuous_const.mul (continuous_norm.pow 2)).neg.measurable)
  refine ⟨fun t => hmeasS.stronglyMeasurable.smul (hUm t),
    fun ξ => ENNReal.ofReal (ν * ‖ξ‖ ^ 2) * MU ξ, ?_, ?_, fun n => ?_, ?_⟩
  · exact (ENNReal.measurable_ofReal.comp ((continuous_const.mul
      (continuous_norm.pow 2)).measurable)).mul hMU
  · filter_upwards [hUb] with ξ h t ht
    rw [enorm_smul]
    refine mul_le_mul' (le_of_eq ?_) (h t ht)
    rw [heatSym2, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
  · have heq : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * (ENNReal.ofReal (ν * ‖ξ‖ ^ 2) * MU ξ) =
        ENNReal.ofReal ν * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (n + 2)) * MU ξ := by
      have hm2 : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ (n + 2)) * MU ξ :=
        (ENNReal.measurable_ofReal.comp (continuous_norm.pow (n + 2)).measurable).mul hMU
      rw [← lintegral_const_mul _ hm2]
      refine lintegral_congr fun ξ => ?_
      have hc : ENNReal.ofReal (‖ξ‖ ^ n) * ENNReal.ofReal (ν * ‖ξ‖ ^ 2) =
          ENNReal.ofReal ν * ENNReal.ofReal (‖ξ‖ ^ (n + 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hν]
        congr 1; ring
      rw [← mul_assoc, hc, mul_assoc]
    rw [heq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUmom _)
  · filter_upwards [hUc] with ξ h using h.const_smul (heatSym2 ν ξ)

/-! ## The time-derivative hierarchy -/

/-- The hierarchy through level `k`, by structural recursion. -/
def Wv (ν : ℝ) (w : ℝ → ES → ComplexSpace) : ℕ → ℕ → ℝ → ES → ComplexSpace
  | 0 => fun _ => w
  | k + 1 => fun i => if i ≤ k then Wv ν w k i else fun t ξ =>
      heatSym2 ν ξ • Wv ν w k k t ξ +
        ∑ m ∈ Finset.range (k + 1),
          k.choose m • continuousNavierBilinear (Wv ν w k m t) (Wv ν w k (k - m) t) ξ

/-- `W 0 = w`, `W (k+1) = -ν‖ξ‖² W k + ∑_{m ≤ k} C(k,m) Bil(W m, W (k-m))`. -/
def W (ν : ℝ) (w : ℝ → ES → ComplexSpace) (k : ℕ) : ℝ → ES → ComplexSpace := Wv ν w k k

theorem Wv_stable (ν : ℝ) (w : ℝ → ES → ComplexSpace) {k i : ℕ} (h : i ≤ k) :
    Wv ν w (k + 1) i = Wv ν w k i := by
  simp [Wv, h]

theorem Wv_eq (ν : ℝ) (w : ℝ → ES → ComplexSpace) {k i : ℕ} (h : i ≤ k) :
    Wv ν w k i = W ν w i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [← add_assoc, Wv_stable ν w (by omega)]
      exact ih (by omega)

theorem W_zero (ν : ℝ) (w : ℝ → ES → ComplexSpace) : W ν w 0 = w := rfl

theorem W_succ (ν : ℝ) (w : ℝ → ES → ComplexSpace) (k : ℕ) (t : ℝ) (ξ : ES) :
    W ν w (k + 1) t ξ = heatSym2 ν ξ • W ν w k t ξ +
      ∑ i ∈ Finset.range (k + 1),
        k.choose i • continuousNavierBilinear (W ν w i t) (W ν w (k - i) t) ξ := by
  show Wv ν w (k + 1) (k + 1) t ξ = _
  simp only [Wv, show ¬ (k + 1 ≤ k) by omega, if_false]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  rw [Wv_eq ν w hi', Wv_eq ν w (Nat.sub_le k i)]

/-- **Every level of the hierarchy is a majorized continuous family.** -/
theorem good_W {T ν : ℝ} (hν : 0 ≤ ν) {w : ℝ → ES → ComplexSpace} (hw : Good T w) (k : ℕ) :
    Good T (W ν w k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [W_zero]; exact hw
    | succ k =>
      have hfun : W ν w (k + 1) = fun t ξ => heatSym2 ν ξ • W ν w k t ξ +
          ∑ i ∈ Finset.range (k + 1),
            k.choose i • continuousNavierBilinear (W ν w i t) (W ν w (k - i) t) ξ := by
        funext t ξ; exact W_succ ν w k t ξ
      rw [hfun]
      refine good_add (good_heat hν (ih k (Nat.lt_succ_self k))) ?_
      refine good_sum _ fun i hi => ?_
      have hi' : i < k + 1 := Finset.mem_range.mp hi
      exact good_nsmul (good_bil (ih i hi') (ih (k - i) (by omega))) _

/-! ## Differentiation of the hierarchy -/

/-- Frequencywise time derivative on `(0, T)`. -/
def HasTimeDeriv (T : ℝ) (U U' : ℝ → ES → ComplexSpace) : Prop :=
  ∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => U s ξ) (U' t ξ) t

/-- The Fourier Navier symbol as a function of the nine convolution values. -/
def bilOfConv (ξ : ES) (c : Fin 3 → Fin 3 → ℂ) : ComplexSpace :=
  continuousLeray ξ (Complex.I • fun i => ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * c j i)

theorem bilinear_eq_bilOfConv (u v : ES → ComplexSpace) (ξ : ES) :
    continuousNavierBilinear u v ξ = bilOfConv ξ (fun j i =>
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ) := rfl

/-- `bilOfConv ξ` is the restriction of a continuous linear map. -/
def bilCLM (ξ : ES) : (Fin 3 → Fin 3 → ℂ) →L[ℂ] ComplexSpace :=
  (LinearMap.toContinuousLinearMap (Navier.Analysis.ComplexLerayProjection.complexLeray
    (Navier.Analysis.FourierMajorant.spaceProj ξ))).comp
    (Complex.I • (ContinuousLinearMap.pi fun i => ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) •
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 3 => Fin 3 → ℂ) j))))

theorem bilCLM_apply (ξ : ES) (c : Fin 3 → Fin 3 → ℂ) : bilCLM ξ c = bilOfConv ξ c := by
  simp [bilCLM, bilOfConv, continuousLeray, smul_eq_mul]

/-- Dominated differentiation of one convolution coordinate. -/
theorem hasDerivAt_conv_coord {T : ℝ} {U U' V V' : ℝ → ES → ComplexSpace}
    (hUm : ∀ t, StronglyMeasurable (U t)) (hU'm : ∀ t, StronglyMeasurable (U' t))
    (hVm : ∀ t, StronglyMeasurable (V t)) (hV'm : ∀ t, StronglyMeasurable (V' t))
    {MU MU' MV MV' : ES → ℝ≥0∞} (hMU : Measurable MU) (hMU' : Measurable MU')
    (hMV : Measurable MV) (hMV' : Measurable MV')
    (hUb : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖U t η‖ₑ ≤ MU η)
    (hU'b : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖U' t η‖ₑ ≤ MU' η)
    (hVb : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖V t η‖ₑ ≤ MV η)
    (hV'b : ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖V' t η‖ₑ ≤ MV' η)
    (hUd : HasTimeDeriv T U U') (hVd : HasTimeDeriv T V V') {ξ : ES}
    (h1 : ∫⁻ η, MU η * MV (ξ - η) ≠ ⊤) (h2 : ∫⁻ η, MU' η * MV (ξ - η) ≠ ⊤)
    (h3 : ∫⁻ η, MU η * MV' (ξ - η) ≠ ⊤) (j i : Fin 3) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun t => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => V t η i)) ξ)
      (((fun η => U' t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V t₀ η i)) ξ +
        ((fun η => U t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V' t₀ η i)) ξ)
      t₀ := by
  have hsub : Measurable fun η : ES => ξ - η := measurable_const.sub measurable_id
  set F : ℝ → ES → ℂ := fun t η => U t η j * V t (ξ - η) i with hF
  set F' : ℝ → ES → ℂ := fun t η => U' t η j * V t (ξ - η) i + U t η j * V' t (ξ - η) i
    with hF'
  have hmeas : ∀ (A B : ℝ → ES → ComplexSpace), (∀ t, StronglyMeasurable (A t)) →
      (∀ t, StronglyMeasurable (B t)) → ∀ t,
      AEStronglyMeasurable (fun η => A t η j * B t (ξ - η) i) volume :=
    fun A B hA hB t => ((((continuous_apply j).comp_stronglyMeasurable (hA t)).mul
      (((continuous_apply i).comp_stronglyMeasurable (hB t)).comp_measurable hsub))).aestronglyMeasurable
  have hbnd : ∀ (A B : ℝ → ES → ComplexSpace) (MA MB : ES → ℝ≥0∞),
      Measurable MA → Measurable MB →
      (∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖A t η‖ₑ ≤ MA η) →
      (∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T, ‖B t η‖ₑ ≤ MB η) →
      ∫⁻ η, MA η * MB (ξ - η) ≠ ⊤ →
      ∀ᵐ η ∂(volume : Measure ES), ∀ t ∈ Icc (0 : ℝ) T,
        ‖A t η j * B t (ξ - η) i‖ ≤ (MA η * MB (ξ - η)).toReal := by
    intro A B MA MB hMA hMB hA hB hfin
    have hfinpt : ∀ᵐ η ∂(volume : Measure ES), MA η * MB (ξ - η) < ⊤ :=
      ae_lt_top (hMA.mul (hMB.comp hsub)) hfin
    filter_upwards [hA, ae_sub_left hB ξ, hfinpt] with η ha hb hf t ht
    have hx : ‖A t η j * B t (ξ - η) i‖ₑ ≤ MA η * MB (ξ - η) := by
      rw [enorm_mul]
      exact mul_le_mul' ((enorm_coord_le _ j).trans (ha t ht))
        ((enorm_coord_le _ i).trans (hb t ht))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono hf.ne hx
  have hint : ∀ (MA MB : ES → ℝ≥0∞), Measurable MA → Measurable MB →
      ∫⁻ η, MA η * MB (ξ - η) ≠ ⊤ → Integrable (fun η => (MA η * MB (ξ - η)).toReal) :=
    fun MA MB hMA hMB hfin =>
      integrable_toReal_of_lintegral_ne_top (hMA.mul (hMB.comp hsub)).aemeasurable hfin
  have hIoo : Ioo (0 : ℝ) T ⊆ Icc (0 : ℝ) T := Ioo_subset_Icc_self
  have hb1 := hbnd U V MU MV hMU hMV hUb hVb h1
  have hb2 := hbnd U' V MU' MV hMU' hMV hU'b hVb h2
  have hb3 := hbnd U V' MU MV' hMU hMV' hUb hV'b h3
  have hFint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (F t) := fun t ht =>
    (hint MU MV hMU hMV h1).mono' (hmeas U V hUm hVm t)
      (by filter_upwards [hb1] with η h using h t ht)
  have hA1 : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun η => U' t η j * V t (ξ - η) i) :=
    fun t ht => (hint MU' MV hMU' hMV h2).mono' (hmeas U' V hU'm hVm t)
      (by filter_upwards [hb2] with η h using h t ht)
  have hA2 : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun η => U t η j * V' t (ξ - η) i) :=
    fun t ht => (hint MU MV' hMU hMV' h3).mono' (hmeas U V' hUm hV'm t)
      (by filter_upwards [hb3] with η h using h t ht)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := t₀) (bound := fun η => (MU' η * MV (ξ - η)).toReal + (MU η * MV' (ξ - η)).toReal)
    (Ioo_mem_nhds ht₀.1 ht₀.2) (Eventually.of_forall fun t => hmeas U V hUm hVm t)
    (hFint t₀ (hIoo ht₀)) ((hmeas U' V hU'm hVm t₀).add (hmeas U V' hUm hV'm t₀))
    (by filter_upwards [hb2, hb3] with η h h' t ht
        exact (norm_add_le _ _).trans (add_le_add (h t (hIoo ht)) (h' t (hIoo ht))))
    ((hint MU' MV hMU' hMV h2).add (hint MU MV' hMU hMV' h3))
    (by filter_upwards [hUd, ae_sub_left hVd ξ] with η hu hv t ht
        have hu' := (hasDerivAt_pi.mp (hu t ht)) j
        have hv' := (hasDerivAt_pi.mp (hv t ht)) i
        exact (hu'.mul hv').congr_deriv (by ring))
  have hconv : ∀ (A B : ℝ → ES → ComplexSpace) (t : ℝ),
      ((fun η => A t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => B t η i)) ξ =
        ∫ η, A t η j * B t (ξ - η) i := fun A B t => by simp [convolution_def]
  have hfun : (fun t => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun η => V t η i)) ξ) = fun t => ∫ η, F t η := funext fun t => hconv U V t
  rw [hfun, hconv U' V t₀, hconv U V' t₀,
    ← integral_add (hA1 t₀ (hIoo ht₀)) (hA2 t₀ (hIoo ht₀))]
  exact hd.2

/-- **Product rule for the Fourier Navier symbol along the hierarchy.** -/
theorem hasTimeDeriv_bil {T : ℝ} {U U' V V' : ℝ → ES → ComplexSpace}
    (hU : Good T U) (hU' : Good T U') (hV : Good T V) (hV' : Good T V')
    (hUd : HasTimeDeriv T U U') (hVd : HasTimeDeriv T V V') :
    HasTimeDeriv T (fun t => continuousNavierBilinear (U t) (V t))
      (fun t ξ => continuousNavierBilinear (U' t) (V t) ξ +
        continuousNavierBilinear (U t) (V' t) ξ) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, -⟩ := hU
  obtain ⟨hU'm, MU', hMU', hU'b, hU'mom, -⟩ := hU'
  obtain ⟨hVm, MV, hMV, hVb, hVmom, -⟩ := hV
  obtain ⟨hV'm, MV', hMV', hV'b, hV'mom, -⟩ := hV'
  filter_upwards [ae_convMaj_ne_top hMU hMV (lintegral_ne_top_of_mom hUmom)
      (lintegral_ne_top_of_mom hVmom),
    ae_convMaj_ne_top hMU' hMV (lintegral_ne_top_of_mom hU'mom) (lintegral_ne_top_of_mom hVmom),
    ae_convMaj_ne_top hMU hMV' (lintegral_ne_top_of_mom hUmom) (lintegral_ne_top_of_mom hV'mom)]
    with ξ h1 h2 h3 t₀ ht₀
  set c : ℝ → Fin 3 → Fin 3 → ℂ := fun t j i =>
    ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V t η i)) ξ with hc
  set c₁ : Fin 3 → Fin 3 → ℂ := fun j i =>
    ((fun η => U' t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V t₀ η i)) ξ
  set c₂ : Fin 3 → Fin 3 → ℂ := fun j i =>
    ((fun η => U t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V' t₀ η i)) ξ
  have hcd : HasDerivAt c (c₁ + c₂) t₀ := by
    refine hasDerivAt_pi.mpr fun j => hasDerivAt_pi.mpr fun i => ?_
    exact hasDerivAt_conv_coord hUm hU'm hVm hV'm hMU hMU' hMV hMV' hUb hU'b hVb hV'b hUd hVd
      h1 h2 h3 j i ht₀
  have hL := ((bilCLM ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hcd
  have hfun : (fun s => continuousNavierBilinear (U s) (V s) ξ) =
      ((bilCLM ξ).restrictScalars ℝ) ∘ c := by
    funext s
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', bilCLM_apply]
    rfl
  rw [hfun]
  refine hL.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', map_add, bilCLM_apply]
  rfl

theorem hasTimeDeriv_add {T : ℝ} {U U' V V' : ℝ → ES → ComplexSpace}
    (hU : HasTimeDeriv T U U') (hV : HasTimeDeriv T V V') :
    HasTimeDeriv T (fun t ξ => U t ξ + V t ξ) (fun t ξ => U' t ξ + V' t ξ) := by
  filter_upwards [hU, hV] with ξ h1 h2 t ht using (h1 t ht).add (h2 t ht)

theorem hasTimeDeriv_nsmul {T : ℝ} {U U' : ℝ → ES → ComplexSpace}
    (hU : HasTimeDeriv T U U') (c : ℕ) :
    HasTimeDeriv T (fun t ξ => c • U t ξ) (fun t ξ => c • U' t ξ) := by
  filter_upwards [hU] with ξ h t ht using (h t ht).const_smul c

theorem hasTimeDeriv_sum {T : ℝ} {ι : Type*} (s : Finset ι) {U U' : ι → ℝ → ES → ComplexSpace}
    (hU : ∀ i ∈ s, HasTimeDeriv T (U i) (U' i)) :
    HasTimeDeriv T (fun t ξ => ∑ i ∈ s, U i t ξ) (fun t ξ => ∑ i ∈ s, U' i t ξ) := by
  have h : ∀ᵐ ξ ∂(volume : Measure ES), ∀ i ∈ s, ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => U i r ξ) (U' i t ξ) t :=
    (ae_ball_iff s.countable_toSet).mpr fun i hi => hU i hi
  filter_upwards [h] with ξ hξ t ht
  exact HasDerivAt.fun_sum fun i hi => hξ i hi t ht

theorem hasTimeDeriv_heat {T ν : ℝ} {U U' : ℝ → ES → ComplexSpace}
    (hU : HasTimeDeriv T U U') :
    HasTimeDeriv T (fun t ξ => heatSym2 ν ξ • U t ξ) (fun t ξ => heatSym2 ν ξ • U' t ξ) := by
  filter_upwards [hU] with ξ h t ht using (h t ht).const_smul (heatSym2 ν ξ)

/-- **The hierarchy is a derivative tower**: if `w` has derivative `W 1`, then
each level `W k` has derivative `W (k+1)`, frequencywise on `(0, T)`. -/
theorem hasTimeDeriv_W {T ν : ℝ} (hν : 0 ≤ ν) {w : ℝ → ES → ComplexSpace} (hw : Good T w)
    (h0 : HasTimeDeriv T (W ν w 0) (W ν w 1)) (k : ℕ) :
    HasTimeDeriv T (W ν w k) (W ν w (k + 1)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => exact h0
    | succ k =>
      have hG := good_W hν hw
      have hfun : W ν w (k + 1) = fun t ξ => heatSym2 ν ξ • W ν w k t ξ +
          ∑ i ∈ Finset.range (k + 1),
            k.choose i • continuousNavierBilinear (W ν w i t) (W ν w (k - i) t) ξ := by
        funext t ξ; exact W_succ ν w k t ξ
      have hd := hasTimeDeriv_add (hasTimeDeriv_heat (ν := ν) (ih k (Nat.lt_succ_self k)))
        (hasTimeDeriv_sum (Finset.range (k + 1)) (U := fun i t ξ =>
          k.choose i • continuousNavierBilinear (W ν w i t) (W ν w (k - i) t) ξ)
          (U' := fun i t ξ => k.choose i • (continuousNavierBilinear (W ν w (i + 1) t)
            (W ν w (k - i) t) ξ + continuousNavierBilinear (W ν w i t) (W ν w (k - i + 1) t) ξ))
          fun i hi => by
            have hi' : i < k + 1 := Finset.mem_range.mp hi
            exact hasTimeDeriv_nsmul (hasTimeDeriv_bil (hG i) (hG (i + 1)) (hG (k - i))
              (hG (k - i + 1)) (ih i hi') (ih (k - i) (by omega))) _)
      rw [hfun]
      filter_upwards [hd] with ξ hξ t ht
      refine (hξ t ht).congr_deriv ?_
      rw [W_succ ν w (k + 1) t ξ]
      congr 1
      rw [Finset.sum_choose_succ_nsmul
        (fun a b => continuousNavierBilinear (W ν w a t) (W ν w b t) ξ) k, add_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [smul_add, show k - i + 1 = 1 + k - i by
        have := Finset.mem_range.mp hi; omega, add_comm]

/-! ## The base of the tower: the mild fixed point solves the frequency ODE -/

open Navier.Analysis.ContinuousLeiLinSelfMap Navier.Analysis.ContinuousLeiLinTimeDuhamel
  Navier.Analysis.ContinuousLeiLinFrequencyODE in
/-- A pointwise mild fixed point on `[0,T]` whose source is continuous in time
has derivative `W 1` frequencywise on `(0,T)`. -/
theorem hasTimeDeriv_W_zero {T ν : ℝ} (hν : 0 < ν) (a : ES → ComplexSpace)
    {w : ℝ → ES → ComplexSpace}
    (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
    (hG : Good T w) : HasTimeDeriv T (W ν w 0) (W ν w 1) := by
  obtain ⟨-, -, -, -, -, hBc⟩ := good_bil hG hG
  filter_upwards [hBc] with ξ hc t₀ ht₀
  have hIcc : Icc (0 : ℝ) T ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  have hws : ∀ i : Fin 3, ContinuousOn (weightedSource ν w w ξ i) (Icc (0 : ℝ) T) := by
    intro i
    unfold weightedSource continuousNavierSource
    exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn).smul
      ((continuous_apply i).comp_continuousOn hc)
  have hd := hasDerivAt_continuousMildImage ν hν a w t₀ ht₀.1 ξ
    (fun i => ((hws i).mono (Icc_subset_Icc_right ht₀.2.le)).intervalIntegrable_of_Icc
      ht₀.1.le)
    (fun i => ((hws i).mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t₀ ht₀)
    (fun i => (hws i).continuousAt hIcc)
  have hev : (fun t => continuousMildImage ν hν a w t ξ) =ᶠ[𝓝 t₀] fun t => W ν w 0 t ξ := by
    filter_upwards [hIcc] with t ht
    rw [W_zero, ← hfix t ht ξ]
  refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [W_succ, W_zero, ← hfix t₀ (Ioo_subset_Icc_self ht₀) ξ]
  simp only [Finset.sum_range_one, Nat.choose_zero_right, one_smul, Nat.sub_zero, W_zero,
    heatSym2, continuousNavierSource]
  push_cast
  rw [Finset.sum_range_one]
  simp [W_zero]

/-! ## From interior derivatives to derivatives within `[0,T]` and a Taylor bound -/

theorem hasDerivWithinAt_Icc_of_interior {T : ℝ} (hT : 0 < T) {f f' : ℝ → ComplexSpace}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hf' : ContinuousOn f' (Icc (0 : ℝ) T))
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt f (f' t) t) :
    ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc (0 : ℝ) T) t := by
  have hdiff : DifferentiableOn ℝ f (Ioo (0 : ℝ) T) := fun t ht =>
    (hd t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, deriv f t = f' t := fun t ht => (hd t ht).deriv
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    have hlim : Tendsto (fun x => deriv f x) (𝓝[>] (0 : ℝ)) (𝓝 (f' 0)) := by
      have hc : Tendsto f' (𝓝[>] (0 : ℝ)) (𝓝 (f' 0)) :=
        ((hf' 0 ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hT)).tendsto
      refine hc.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hT] with x hx using (hderiv x hx).symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff ((hf 0 ht).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hT) hlim).mono Icc_subset_Ici_self
  · rcases eq_or_lt_of_le ht.2 with hTe | hlt
    · subst hTe
      have hlim : Tendsto (fun x => deriv f x) (𝓝[<] t) (𝓝 (f' t)) := by
        have hc : Tendsto f' (𝓝[<] t) (𝓝 (f' t)) :=
          ((hf' t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hpos)).tendsto
        refine hc.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hpos] with x hx using (hderiv x hx).symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff ((hf t ht).mono Ioo_subset_Icc_self)
        (Ioo_mem_nhdsLT hpos) hlim).mono Icc_subset_Iic_self
    · exact (hd t ⟨hpos, hlt⟩).hasDerivWithinAt

/-- Second-order Taylor bound on `[0,T]` from within-derivatives and a bound on
the second derivative. -/
theorem norm_taylor_le {T B : ℝ} {f f' f'' : ℝ → ComplexSpace}
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc (0 : ℝ) T) t)
    (hd' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f' (f'' t) (Icc (0 : ℝ) T) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ‖f'' t‖ ≤ B) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ht' : t' ∈ Icc (0 : ℝ) T) :
    ‖f t' - f t - (t' - t) • f' t‖ ≤ B * (t' - t) ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hconv : Convex ℝ (Icc (0 : ℝ) T) := convex_Icc 0 T
  have hmv1 : ∀ s ∈ Icc (0 : ℝ) T, ‖f' s - f' t‖ ≤ B * ‖s - t‖ := fun s hs =>
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd' hB ht hs
  set φ : ℝ → ComplexSpace := fun s => f s - f t - (s - t) • f' t with hφ
  have hφd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt φ (f' s - f' t) (Icc (0 : ℝ) T) s := by
    intro s hs
    have h := ((hd s hs).sub_const (f t)).sub (((hasDerivAt_id s).sub_const t).smul_const
      (f' t)).hasDerivWithinAt
    refine h.congr_deriv ?_
    simp
  have hsub : uIcc t t' ⊆ Icc (0 : ℝ) T := uIcc_subset_Icc ht ht'
  have hbound : ∀ s ∈ uIcc t t', ‖f' s - f' t‖ ≤ B * |t' - t| := by
    intro s hs
    refine (hmv1 s (hsub hs)).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [Real.norm_eq_abs]
    exact abs_sub_left_of_mem_uIcc hs
  have hmvt := (convex_uIcc t t').norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hφd s (hsub hs)).mono hsub) hbound left_mem_uIcc right_mem_uIcc
  have hφt : φ t = 0 := by simp [hφ]
  rw [hφt, sub_zero, Real.norm_eq_abs] at hmvt
  calc ‖φ t'‖ ≤ B * |t' - t| * |t' - t| := hmvt
    _ = B * (t' - t) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ## A derivative tower yields a smooth Fourier path -/

section Tower

open Navier.Analysis.WienerL1Carrier Navier.Analysis.WienerSmoothPath

variable {T : ℝ} (hT : 0 < T) (U : ℕ → ℝ → ES → ComplexSpace) (hG : ∀ k, Good T (U k))
  (i : Fin 3)

/-- The `i`-th coordinate of `ξ^α U k`, with time clamped to `[0,T]`. -/
def towerSym (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) (ξ : ES) : ℂ :=
  mono α ξ * U k (projIcc 0 T hT.le t) ξ i

include hG in
theorem integrable_towerSym (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) :
    Integrable (towerSym hT U i k α t) := by
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hG k
  have hwm : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ :=
    (ENNReal.measurable_ofReal.comp (continuous_norm.pow _).measurable).mul hM
  have hg : Integrable fun ξ : ES => (ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ).toReal :=
    integrable_toReal_of_lintegral_ne_top hwm.aemeasurable (hmom (deg α))
  refine hg.mono' ?_ ?_
  · unfold towerSym mono
    exact ((by fun_prop : Continuous fun ξ : ES => ∏ j : Fin 3, ((ξ j : ℝ) : ℂ) ^ (α j)).aestronglyMeasurable).mul
      ((continuous_apply i).comp_stronglyMeasurable (hm _)).aestronglyMeasurable
  · filter_upwards [hb, ae_lt_top hwm (hmom (deg α))] with ξ h hfin
    have hx : ‖towerSym hT U i k α t ξ‖ₑ ≤ ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ := by
      unfold towerSym
      rw [enorm_mul]
      refine mul_le_mul' ?_ ((enorm_coord_le _ i).trans (h _ (projIcc 0 T hT.le t).2))
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_mono_le α ξ)
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono hfin.ne hx

/-- The coefficient classes of the tower. -/
def towerD (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) : L1C :=
  (integrable_towerSym hT U hG i k α t).toL1 _

theorem coeFn_towerD (k : ℕ) (α : Fin 3 → ℕ) (t : ℝ) :
    ⇑(towerD hT U hG i k α t) =ᵐ[volume] towerSym hT U i k α t :=
  Integrable.coeFn_toL1 _

theorem towerD_mul (k : ℕ) (α : Fin 3 → ℕ) (j : Fin 3) (t : ℝ) :
    ⇑(towerD hT U hG i k (α + ej j) t) =ᵐ[volume]
      fun ξ : ES => ((ξ j : ℝ) : ℂ) * towerD hT U hG i k α t ξ := by
  filter_upwards [coeFn_towerD hT U hG i k (α + ej j) t, coeFn_towerD hT U hG i k α t]
    with ξ h1 h2
  rw [h1, h2]
  unfold towerSym
  rw [mono_add_ej]
  ring

include hG in
theorem towerD_deriv (hd : ∀ k, HasTimeDeriv T (U k) (U (k + 1))) (k : ℕ) (α : Fin 3 → ℕ)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (towerD hT U hG i k α) (towerD hT U hG i (k + 1) α t) (Ico (0 : ℝ) T) t := by
  obtain ⟨-, M, hM, hb, hmom, -⟩ := hG (k + 2)
  obtain ⟨-, -, -, -, -, hc0⟩ := hG k
  obtain ⟨-, -, -, -, -, hc1⟩ := hG (k + 1)
  obtain ⟨-, -, -, -, -, hc2⟩ := hG (k + 2)
  have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
  have hwm : Measurable fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ :=
    (ENNReal.measurable_ofReal.comp (continuous_norm.pow _).measurable).mul hM
  set C : ℝ := ∫ ξ, (ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ).toReal with hC
  -- pointwise Taylor bound
  have hpt : ∀ᵐ ξ ∂(volume : Measure ES), ∀ t' ∈ Icc (0 : ℝ) T,
      ‖towerSym hT U i k α t' ξ - towerSym hT U i k α t ξ -
          (t' - t) • towerSym hT U i (k + 1) α t ξ‖ ≤
        (ENNReal.ofReal (‖ξ‖ ^ deg α) * M ξ).toReal * (t' - t) ^ 2 := by
    filter_upwards [hc0, hc1, hc2, hd k, hd (k + 1), hb, ae_lt_top hM
      (by simpa using hmom 0)] with ξ h0 h1 h2 hk hk1 hbd hfin t' ht'
    have hD0 := hasDerivWithinAt_Icc_of_interior hT h0 h1 hk
    have hD1 := hasDerivWithinAt_Icc_of_interior hT h1 h2 hk1
    have hB : ∀ s ∈ Icc (0 : ℝ) T, ‖U (k + 2) s ξ‖ ≤ (M ξ).toReal := fun s hs => by
      rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
      exact ENNReal.toReal_mono hfin.ne (hbd s hs)
    have hT2 := norm_taylor_le hD0 hD1 hB htI ht'
    have hproj : ∀ s ∈ Icc (0 : ℝ) T, projIcc 0 T hT.le s = s := fun s hs => by
      rw [projIcc_of_mem hT.le hs]
    unfold towerSym
    rw [hproj t' ht', hproj t htI]
    have heq : mono α ξ * U k t' ξ i - mono α ξ * U k t ξ i - (t' - t) • (mono α ξ *
        U (k + 1) t ξ i) = mono α ξ * (U k t' ξ - U k t ξ - (t' - t) • U (k + 1) t ξ) i := by
      simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]; ring
    rw [heq, norm_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hm := norm_mono_le α ξ
    calc ‖mono α ξ‖ * ‖(U k t' ξ - U k t ξ - (t' - t) • U (k + 1) t ξ) i‖
        ≤ ‖ξ‖ ^ deg α * ((M ξ).toReal * (t' - t) ^ 2) :=
          mul_le_mul hm ((norm_le_pi_norm _ i).trans hT2) (norm_nonneg _) (by positivity)
      _ = ‖ξ‖ ^ deg α * (M ξ).toReal * (t' - t) ^ 2 := by ring
  have hbound : ∀ t' ∈ Icc (0 : ℝ) T,
      ‖towerD hT U hG i k α t' - towerD hT U hG i k α t - (t' - t) • towerD hT U hG i (k + 1) α t‖
        ≤ C * ‖t' - t‖ ^ 2 := by
    intro t' ht'
    rw [L1.norm_eq_integral_norm]
    have hae : (fun ξ => ‖(towerD hT U hG i k α t' - towerD hT U hG i k α t -
        (t' - t) • towerD hT U hG i (k + 1) α t : L1C) ξ‖) =ᵐ[volume]
        fun ξ => ‖towerSym hT U i k α t' ξ - towerSym hT U i k α t ξ -
          (t' - t) • towerSym hT U i (k + 1) α t ξ‖ := by
      filter_upwards [Lp.coeFn_sub (towerD hT U hG i k α t' - towerD hT U hG i k α t)
          ((t' - t) • towerD hT U hG i (k + 1) α t),
        Lp.coeFn_sub (towerD hT U hG i k α t') (towerD hT U hG i k α t),
        Lp.coeFn_smul (t' - t) (towerD hT U hG i (k + 1) α t),
        coeFn_towerD hT U hG i k α t', coeFn_towerD hT U hG i k α t,
        coeFn_towerD hT U hG i (k + 1) α t] with ξ h1 h2 h3 h4 h5 h6
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h5, h6]
    rw [integral_congr_ae hae, Real.norm_eq_abs, sq_abs, hC, ← integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrable_toReal_of_lintegral_ne_top hwm.aemeasurable (hmom (deg α))).mul_const _) ?_
    filter_upwards [hpt] with ξ h using h t' ht'
  rw [hasDerivWithinAt_iff_isLittleO]
  have hO : (fun t' => towerD hT U hG i k α t' - towerD hT U hG i k α t -
      (t' - t) • towerD hT U hG i (k + 1) α t) =O[𝓝[Ico (0 : ℝ) T] t]
      fun t' => ‖t' - t‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t' (Ico_subset_Icc_self ht')
  exact hO.trans_isLittleO ((Asymptotics.isLittleO_pow_sub_sub t one_lt_two).mono
    nhdsWithin_le_nhds)

/-- **A derivative tower of majorized continuous families is a smooth Fourier
path, coordinatewise.** -/
def towerPath (hd : ∀ k, HasTimeDeriv T (U k) (U (k + 1))) : SmoothFourierPath T where
  D := towerD hT U hG i
  mul := towerD_mul hT U hG i
  deriv k α _ ht := towerD_deriv hT U hG i hd k α ht

end Tower

/-! ## Consumer: joint smoothness of the physical field of a mild fixed point -/

open Navier.Analysis.ContinuousLeiLinSelfMap Navier.Analysis.WienerSmoothPath in
/-- **A pointwise mild fixed point on `[0,T]` which is a majorized continuous
family has jointly `C^∞` physical coordinates on `[0,T) × ℝ³`.** -/
theorem contDiffOn_physicalCoord_of_mild {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (a : ES → ComplexSpace) {w : ℝ → ES → ComplexSpace}
    (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
    (hG : Good T w) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ES =>
        Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord (w z.1) i z.2)
      (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
  have hGW := good_W hν.le hG
  have hdW := hasTimeDeriv_W hν.le hG (hasTimeDeriv_W_zero hν a hfix hG)
  set P := towerPath hT (W ν w) hGW i hdW
  refine (contDiffOn_phys hT P).congr fun z hz => ?_
  show Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord (w z.1) i z.2 =
    𝓕⁻ (⇑(towerD hT (W ν w) hGW i 0 0 z.1)) z.2
  rw [fourierInv_congr (coeFn_towerD hT (W ν w) hGW i 0 0 z.1) z.2]
  unfold Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord towerSym
  rw [projIcc_of_mem hT.le (Ico_subset_Icc_self hz.1)]
  simp [mono, W_zero]

end Navier.Analysis.WienerPointwiseODE

set_option pp.fullNames true in
#check @Navier.Analysis.WienerPointwiseODE.contDiffOn_physicalCoord_of_mild
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPointwiseODE.contDiffOn_physicalCoord_of_mild
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPointwiseODE.towerPath
