import Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit
import Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
import Navier.Analysis.WholeSpaceHeatThirdDerivative

/-!
# Interval identification of the cutoff-free backward-heat-curl RHS

The exact compact weak-evolution time integrals converge to the cutoff-free
endpoint momentum difference (`WholeSpaceSolenoidalHeatIntegratedRhsLimit`),
and the fixed-time compact-test RHS converges pointwise in the radius to
`backwardHeatCurlRhs` (`WholeSpaceSolenoidalHeatFullViscousLimit`).  This
module removes the last obstruction stated in both files — identifying the
limit of the interval integrals with the interval integral of the pointwise
limit — by dominated convergence in the time variable.

The dominating function is a constant.  The `SolvesBefore.energy_le_initial`
field bounds `∫ ‖u t‖²` by the initial kinetic energy uniformly in the time
variable on `[0, T)`; every spatial derivative of the cutoff test is
pointwise bounded by a fixed combination of positive-time Gaussian
translates (cutoff derivatives carry only `R⁻¹, R⁻², R⁻³` factors, absorbed
at `R ≥ 1`, and the Gaussian derivatives are dominated by wider Gaussians —
see `exists_abs_fderiv_heatKernel_translate_le_doubled`,
`exists_abs_second_heatKernel_le_gaussians`,
`exists_abs_third_heatKernel_le_gaussians`); and a positive-time Gaussian
translate has finite sup-norm and finite `L²` mass.  A constant majorant is
integrable on the finite interval `(ta, tb]`, so the interchange needs no
time-uniform continuity of the solution.  This is the standard
Gaussian-test domination argument (Majda–Bertozzi, *Vorticity and
Incompressible Flow*, §3.3, adapted to the repository's concrete
`curl (χ_R G_τ a)` family).
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval BigOperators Matrix
open MeasureTheory Filter Set

namespace Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity
open Navier.Analysis.CurlIdentities
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatConvectionLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.CurlDerivativeBridge
open Navier.Analysis.WholeSpaceHeatThirdDerivative
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability
open Navier.Breakdown

/-! ## Energy and norm bridges -/

theorem kineticEnergy_eq_integral_officialEuclideanNorm_sq
    (u : VelocityEvolution) (t : ℝ) :
    kineticEnergy u t = ∫ x : Space, officialEuclideanNorm (u t x) ^ 2 := by
  unfold kineticEnergy
  congr 1
  funext x
  exact (officialEuclideanNorm_sq_eq_sum_sq (u t x)).symm

/-- The sup-norm squared slice integral is dominated by the official energy,
hence by the initial energy on every preterminal slice. -/
theorem SolvesBefore.integral_supNorm_sq_le {ν T : ℝ} {u : VelocityEvolution}
    {p : PressureEvolution} (hsol : SolvesBefore ν T u p)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    ∫ x : Space, ‖u t x‖ ^ 2 ≤ kineticEnergy u 0 := by
  have hu : ContDiff ℝ ∞ (u t) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 ht0 htT y
  have hfin := hsol.finite_energy t ht0 htT
  have hoff : Integrable (fun x => officialEuclideanNorm (u t x) ^ 2) :=
    (integrable_norm_sq_iff_officialEuclideanNorm_sq (u t)
      hu.continuous.aestronglyMeasurable).mp hfin
  have hae : (fun x : Space => ‖u t x‖ ^ 2) ≤ᵐ[volume]
      fun x => officialEuclideanNorm (u t x) ^ 2 := by
    filter_upwards with x
    exact norm_sq_le_officialEuclideanNorm_sq (u t x)
  have hmono : ∫ x : Space, ‖u t x‖ ^ 2 ≤
      ∫ x : Space, officialEuclideanNorm (u t x) ^ 2 :=
    MeasureTheory.integral_mono_ae hfin hoff hae
  have hle : ∫ x : Space, officialEuclideanNorm (u t x) ^ 2 ≤
      kineticEnergy u 0 := by
    rw [← kineticEnergy_eq_integral_officialEuclideanNorm_sq u t]
    exact hsol.energy_le_initial t ht0 htT
  exact hmono.trans hle

/-! ## Stage 1: the uniform (constant) majorant for the fixed-time RHS -/

private theorem vec_expand (v : Space) :
    v = ∑ i : Fin 3, v i • basisVector i := by
  ext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [basisVector]
  · intro i _ hne
    simp [basisVector, hne]
  · simp

private theorem clm_apply_basisExpansion
    (L : Space →L[ℝ] ℝ) (v : Space) :
    L v = ∑ i : Fin 3, (v i : ℝ) • L (basisVector i) := by
  conv_lhs => rw [vec_expand v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul]

/-- The coordinate second derivatives of a translated positive-time Gaussian
are dominated by two wider translated Gaussians, uniformly in the pair. -/
private theorem exists_abs_second_heatKernel_translate_le_gaussians
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (y : Space) (i j : Fin 3),
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector i))
          y (basisVector j)| ≤
        A * heatKernel κ (4 * τ) (x₀ - y) + B * heatKernel κ τ (x₀ - y) := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_abs_second_heatKernel_le_gaussians hκ hτ
  refine ⟨A, B, hA, hB, fun y i j => ?_⟩
  rw [fderiv_fderiv_heatKernel_translate_apply]
  exact h (x₀ - y) i j

/-- The coordinate third derivatives of a translated positive-time Gaussian
are dominated by two wider translated Gaussians, uniformly in the triple. -/
private theorem exists_abs_third_heatKernel_translate_le_gaussians
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (y : Space) (i j k : Fin 3),
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun z' : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z'
                  (basisVector i))
              z (basisVector j))
          y (basisVector k)| ≤
        A * heatKernel κ (8 * τ) (x₀ - y) +
          B * heatKernel κ (2 * τ) (x₀ - y) := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_abs_third_heatKernel_le_gaussians hκ hτ
  refine ⟨A, B, hA, hB, fun y i j k => ?_⟩
  rw [fderiv_fderiv_fderiv_heatKernel_translate_apply, abs_neg]
  exact h (x₀ - y) i j k

/-! ### Directional derivative plumbing -/

/-- The first coordinate derivative of a product of two smooth scalar
fields. -/
private theorem firstDirectional_mul
    {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => f y * g y) x (basisVector direction) =
      fderiv ℝ f x (basisVector direction) * g x +
        f x * fderiv ℝ g x (basisVector direction) := by
  change (fderiv ℝ (f * g) x) (basisVector direction) = _
  rw [fderiv_mul ((hf.differentiable (by norm_num)).differentiableAt)
    ((hg.differentiable (by norm_num)).differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Two diagonal directional derivatives distribute over a sum of smooth
scalar fields. -/
private theorem secondDirectional_add
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ (fun y : Space => F y + H y) z
      (basisVector direction)) x (basisVector direction) =
      fderiv ℝ (fun z : Space => fderiv ℝ F z (basisVector direction))
        x (basisVector direction) +
      fderiv ℝ (fun z : Space => fderiv ℝ H z (basisVector direction))
        x (basisVector direction) := by
  have hfirst : (fun z : Space => fderiv ℝ (fun y : Space => F y + H y) z
      (basisVector direction)) = fun z : Space =>
        fderiv ℝ F z (basisVector direction) +
          fderiv ℝ H z (basisVector direction) := by
    funext z
    rw [fderiv_fun_add
      ((hF.differentiable (by norm_num)).differentiableAt)
      ((hH.differentiable (by norm_num)).differentiableAt)]
    rfl
  rw [hfirst]
  have hDF : ContDiff ℝ ∞ (fun z : Space =>
      fderiv ℝ F z (basisVector direction)) :=
    contDiff_fderiv_apply hF (basisVector direction)
  have hDH : ContDiff ℝ ∞ (fun z : Space =>
      fderiv ℝ H z (basisVector direction)) :=
    contDiff_fderiv_apply hH (basisVector direction)
  rw [fderiv_fun_add
    ((hDF.differentiable (by norm_num)).differentiableAt)
    ((hDH.differentiable (by norm_num)).differentiableAt)]
  rfl

/-- One coordinate derivative of a constant linear combination. -/
private theorem firstDirectional_sub_smul
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c₁ c₂ : ℝ) (v : Space) (x : Space) :
    fderiv ℝ (fun y : Space => c₁ • F y - c₂ • H y) x v =
      c₁ * fderiv ℝ F x v - c₂ * fderiv ℝ H x v := by
  rw [fderiv_fun_sub
      (((hF.const_smul c₁).differentiable (by norm_num)).differentiableAt)
      (((hH.const_smul c₂).differentiable (by norm_num)).differentiableAt),
    fderiv_fun_const_smul ((hF.differentiable (by norm_num)).differentiableAt)
      c₁,
    fderiv_fun_const_smul ((hH.differentiable (by norm_num)).differentiableAt)
      c₂]
  simp only [sub_apply, smul_apply, smul_eq_mul]

/-- Two diagonal coordinate derivatives of a constant linear combination. -/
private theorem secondDirectional_sub_smul
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c₁ c₂ : ℝ) (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun z : Space =>
        fderiv ℝ (fun y : Space => c₁ • F y - c₂ • H y) z
          (basisVector direction))
      x (basisVector direction) =
      c₁ * fderiv ℝ (fun z : Space => fderiv ℝ F z (basisVector direction))
          x (basisVector direction) -
        c₂ * fderiv ℝ (fun z : Space => fderiv ℝ H z (basisVector direction))
          x (basisVector direction) := by
  have hD1 : (fun z : Space => fderiv ℝ (fun y : Space =>
      c₁ • F y - c₂ • H y) z (basisVector direction)) =
      fun z : Space => c₁ * fderiv ℝ F z (basisVector direction) -
        c₂ * fderiv ℝ H z (basisVector direction) := by
    funext z
    exact firstDirectional_sub_smul hF hH c₁ c₂ (basisVector direction) z
  rw [hD1]
  have hshape : (fun z : Space => c₁ * fderiv ℝ F z (basisVector direction) -
      c₂ * fderiv ℝ H z (basisVector direction)) =
      fun z : Space =>
        c₁ • fderiv ℝ F z (basisVector direction) -
          c₂ • fderiv ℝ H z (basisVector direction) := by
    funext z
    rw [smul_eq_mul, smul_eq_mul]
  rw [hshape]
  have hF1 : ContDiff ℝ ∞ (fun z : Space =>
      fderiv ℝ F z (basisVector direction)) :=
    contDiff_fderiv_apply hF (basisVector direction)
  have hH1 : ContDiff ℝ ∞ (fun z : Space =>
      fderiv ℝ H z (basisVector direction)) :=
    contDiff_fderiv_apply hH (basisVector direction)
  rw [firstDirectional_sub_smul hF1 hH1 c₁ c₂ (basisVector direction) x]

/-- A continuous linear functional bounded by `B` on every basis direction is
bounded by `3 · B · ‖v‖` everywhere. -/
private theorem clm_apply_bound (L : Space →L[ℝ] ℝ) {v : Space} {B : ℝ}
    (h : ∀ i : Fin 3, |L (basisVector i)| ≤ B) :
    |L v| ≤ 3 * B * ‖v‖ := by
  rw [clm_apply_basisExpansion]
  have h1 : |∑ i : Fin 3, (v i : ℝ) • L (basisVector i)| ≤
      ∑ i : Fin 3, |v i| * |L (basisVector i)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => by
        rw [smul_eq_mul, abs_mul])
  have h2 : ∑ i : Fin 3, |v i| * |L (basisVector i)| ≤
      ∑ i : Fin 3, (‖v‖ * B) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm v i))
        (h i) (abs_nonneg _) (norm_nonneg _)
  calc |∑ i : Fin 3, (v i : ℝ) • L (basisVector i)| ≤
        ∑ i : Fin 3, ‖v‖ * B := h1.trans h2
    _ = 3 * B * ‖v‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Triangle inequality for a sum of three real numbers. -/
private theorem abs_sum_three_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : a + b + c = a + (b + c) := add_assoc a b c
  have h2 : (|a| + |b| + |c| : ℝ) = |a| + (|b| + |c|) := add_assoc _ _ _
  rw [h1, h2]
  exact (abs_add_le a (b + c)).trans
    (add_le_add (le_refl _) (abs_add_le b c))

/-- Triangle inequality for a sum of four real numbers. -/
private theorem abs_sum_four_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : a + b + c + d = a + (b + (c + d)) := by simp [add_assoc]
  have h2 : (|a| + |b| + |c| + |d| : ℝ) = |a| + (|b| + (|c| + |d|)) :=
    by simp [add_assoc]
  rw [h1, h2]
  refine (abs_add_le a _).trans ?_
  refine add_le_add (le_refl _) ?_
  refine (abs_add_le b _).trans ?_
  refine add_le_add (le_refl _) ?_
  exact abs_add_le c d

private lemma sq_four_sum_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Inverse-radius factors at radius `max 1 R ≥ 1` are absorbed by one. -/
private lemma inv_absorb (R : ℝ) :
    (max 1 R)⁻¹ ≤ 1 ∧ (max 1 R)⁻¹ * (max 1 R)⁻¹ ≤ 1 ∧
      (max 1 R)⁻¹ * (max 1 R)⁻¹ * (max 1 R)⁻¹ ≤ 1 := by
  have hR0 : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left 1 R)
  have hRinv : (max 1 R)⁻¹ ≤ 1 := (inv_le_one₀ hR0).mpr (le_max_left 1 R)
  have ai : 0 ≤ (max 1 R)⁻¹ := inv_nonneg.mpr hR0.le
  have h2 : (max 1 R)⁻¹ * (max 1 R)⁻¹ ≤ 1 := by
    calc (max 1 R)⁻¹ * (max 1 R)⁻¹ ≤ 1 * (max 1 R)⁻¹ :=
          mul_le_mul_of_nonneg_right hRinv ai
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hRinv zero_le_one
      _ = 1 := by ring
  exact ⟨hRinv, h2, by
    calc (max 1 R)⁻¹ * (max 1 R)⁻¹ * (max 1 R)⁻¹ ≤ 1 * (max 1 R)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 ai
      _ ≤ 1 := by rw [one_mul]; exact hRinv⟩

/-! ### Bounded coordinate second derivatives of the cutoff Gaussian -/

/-- **Radius- and point-uniform bound for the coordinate mixed second
derivatives of the cutoff Gaussian.**  Every `D_i D_k (χ_{max 1 R} G_τ(x₀ −
·))` is bounded by one constant independent of `R` and of the evaluation
point: the `R⁻¹, R⁻²` cutoff rates are absorbed at `max 1 R ≥ 1`, the
cutoff is bounded by one, and the positive-time Gaussian derivatives are
bounded at their peaks. -/
theorem exists_D2_scaledCutoff_heatKernel_uniform_bound
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R : ℝ) (i k : Fin 3) (y : Space),
      |fderiv ℝ
          (fun z : Space => fderiv ℝ
            (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
              (basisVector k))
          y (basisVector i)| ≤ K := by
  obtain ⟨M₁, hM₁₀, hM₁⟩ := standardCutoff_coordinate_derivative_rates.1
  have hM2 : ∀ i j : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
          (basisVector j)| ≤ R⁻¹ * R⁻¹ * M :=
    standardCutoff_coordinate_derivative_rates.2.1
  let M₂ : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hM2 i j)
  have hM₂ : ∀ i j : Fin 3, 0 ≤ M₂ i j ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
          (basisVector j)| ≤ R⁻¹ * R⁻¹ * M₂ i j :=
    fun i j => Classical.choose_spec (hM2 i j)
  obtain ⟨C₁, hC₁, hD1⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  obtain ⟨A₂, B₂, hA₂, hB₂, hD2⟩ :=
    exists_abs_second_heatKernel_translate_le_gaussians hκ hτ x₀
  let M₂sum : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, M₂ i j
  have hM₂sum₀ : 0 ≤ M₂sum :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hM₂ i j).1
  have hM₂le : ∀ i j : Fin 3, M₂ i j ≤ M₂sum := by
    intro i j
    calc M₂ i j ≤ ∑ b : Fin 3, M₂ i b :=
          Finset.single_le_sum (fun b _ => (hM₂ i b).1) (Finset.mem_univ j)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, M₂ a b :=
          Finset.single_le_sum (fun a _ =>
            Finset.sum_nonneg (fun b _ => (hM₂ a b).1)) (Finset.mem_univ i)
  let P₁ : ℝ := (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2)
  let P₂ : ℝ := (4 * Real.pi * κ * (2 * τ)) ^ (-(3 : ℝ) / 2)
  let P₄ : ℝ := (4 * Real.pi * κ * (4 * τ)) ^ (-(3 : ℝ) / 2)
  have hP₁₀ : 0 ≤ P₁ := by
    exact Real.rpow_nonneg (by positivity) _
  have hP₂₀ : 0 ≤ P₂ := by
    exact Real.rpow_nonneg (by positivity) _
  have hP₄₀ : 0 ≤ P₄ := by
    exact Real.rpow_nonneg (by positivity) _
  let K : ℝ := M₂sum * P₁ + 2 * M₁ * C₁ * P₂ + A₂ * P₄ + B₂ * P₁
  refine ⟨K, ?_, ?_⟩
  · show 0 ≤ M₂sum * P₁ + 2 * M₁ * C₁ * P₂ + A₂ * P₄ + B₂ * P₁
    positivity
  · intro R i k y
    obtain ⟨hRinv, hRinv2, _⟩ := inv_absorb R
    have hGτ : 0 ≤ heatKernel κ τ (x₀ - y) := heatKernel_nonneg hκ hτ _
    have hG2τ : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hG4τ : 0 ≤ heatKernel κ (4 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hpeak1 : heatKernel κ τ (x₀ - y) ≤ P₁ :=
      heatKernel_translate_le_peak hκ hτ x₀ y
    have hpeak2 : heatKernel κ (2 * τ) (x₀ - y) ≤ P₂ :=
      heatKernel_translate_le_peak hκ (by positivity) x₀ y
    have hpeak4 : heatKernel κ (4 * τ) (x₀ - y) ≤ P₄ :=
      heatKernel_translate_le_peak hκ (by positivity) x₀ y
    have hχ1 : ∀ m : Fin 3,
        |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector m)| ≤ M₁ := by
      intro m
      calc |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector m)|
          ≤ (max 1 R)⁻¹ * M₁ :=
            hM₁ (R := max 1 R)
              (lt_of_lt_of_le zero_lt_one (le_max_left 1 R)) y m
        _ ≤ 1 * M₁ := mul_le_mul_of_nonneg_right hRinv hM₁₀
        _ = M₁ := one_mul _
    have hχ2 : ∀ a b : Fin 3,
        |fderiv ℝ (fun z : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector a)) y
            (basisVector b)| ≤ M₂ a b := by
      intro a b
      calc |fderiv ℝ (fun z : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector a)) y
            (basisVector b)| ≤ (max 1 R)⁻¹ * (max 1 R)⁻¹ * M₂ a b :=
          (hM₂ a b).2 (R := max 1 R)
            (lt_of_lt_of_le zero_lt_one (le_max_left 1 R)) y
      _ ≤ 1 * (1 * M₂ a b) := by
          rw [show (max 1 R)⁻¹ * (max 1 R)⁻¹ * M₂ a b =
                (max 1 R)⁻¹ * ((max 1 R)⁻¹ * M₂ a b) by ring]
          have hRinv0 : 0 ≤ (max 1 R)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one
              (le_max_left 1 R)))
          refine (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hRinv (hM₂ a b).1) hRinv0).trans
            (mul_le_mul_of_nonneg_right hRinv
              (mul_nonneg zero_le_one (hM₂ a b).1))
      _ = M₂ a b := by ring
    have hG1 : ∀ m : Fin 3,
        |fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
            (basisVector m)| ≤ C₁ * P₂ := by
      intro m
      have := hD1 x₀ y (basisVector m)
      rw [norm_basisVector] at this
      rw [mul_one] at this
      exact this.trans (mul_le_mul_of_nonneg_left hpeak2 (le_of_lt hC₁))
    have hG2 : ∀ a b : Fin 3,
        |fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => heatKernel κ τ (x₀ - w)) z (basisVector a)) y
            (basisVector b)| ≤ A₂ * P₄ + B₂ * P₁ := by
      intro a b
      exact (hD2 y a b).trans (add_le_add
        (mul_le_mul_of_nonneg_left hpeak4 (le_of_lt hA₂))
        (mul_le_mul_of_nonneg_left hpeak1 (le_of_lt hB₂)))
    have hterm1 : |fderiv ℝ (fun z : Space =>
          fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector k)) y
          (basisVector i) * heatKernel κ τ (x₀ - y)| ≤ M₂sum * P₁ := by
      rw [abs_mul, abs_of_nonneg hGτ]
      exact mul_le_mul ((hχ2 k i).trans (hM₂le k i)) hpeak1 hGτ
        hM₂sum₀
    have hterm2 : |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector k) *
          fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
            (basisVector i)| ≤ M₁ * C₁ * P₂ := by
      rw [abs_mul]
      exact (mul_le_mul (hχ1 k) (hG1 i) (abs_nonneg _) hM₁₀).trans
        (le_of_eq (by ring))
    have hterm3 : |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector i) *
          fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
            (basisVector k)| ≤ M₁ * C₁ * P₂ := by
      rw [abs_mul]
      exact (mul_le_mul (hχ1 i) (hG1 k) (abs_nonneg _) hM₁₀).trans
        (le_of_eq (by ring))
    have hterm4 : |scaledCutoff (max 1 R) y * fderiv ℝ
          (fun z : Space => fderiv ℝ
            (fun w : Space => heatKernel κ τ (x₀ - w)) z (basisVector k)) y
            (basisVector i)| ≤ A₂ * P₄ + B₂ * P₁ := by
      rw [abs_mul,
        abs_of_nonneg (scaledCutoff_nonneg (max 1 R) y)]
      exact (mul_le_mul (scaledCutoff_le_one _ _) (hG2 k i) (abs_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul _))
    rw [mixedDirectional_mul (scaledCutoff_contDiff (max 1 R))
      (heatKernel_translate_contDiff κ τ x₀) k i y]
    refine (abs_sum_four_le _ _ _ _).trans ?_
    exact (add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4).trans
      (le_of_eq (by
        show ((M₂sum * P₁ + M₁ * C₁ * P₂) + M₁ * C₁ * P₂) +
            (A₂ * P₄ + B₂ * P₁) =
          M₂sum * P₁ + 2 * M₁ * C₁ * P₂ + A₂ * P₄ + B₂ * P₁
        ring))

/-! ### Gaussian envelope for the coordinate third derivatives -/

/-- **Gaussian envelope for the coordinate third derivatives of the cutoff
Gaussian.**  Every `D_i D_i D_k (χ_{max 1 R} G_τ(x₀ − ·))` is dominated
pointwise by one fixed summable combination of positive-time Gaussian
translates, independent of the radius: the cutoff rates are absorbed at
`max 1 R ≥ 1`, the cutoff itself is bounded by one, and the Gaussian
derivatives are dominated by wider Gaussians. -/
theorem exists_D3_scaledCutoff_heatKernel_envelope
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) :
    ∃ E : Space → ℝ,
      (∀ y : Space, 0 ≤ E y) ∧
        Integrable (fun y : Space => E y ^ 2) ∧
          ∀ (R : ℝ) (i k : Fin 3) (y : Space),
            |fderiv ℝ
                (fun z : Space => fderiv ℝ
                  (fun z' : Space => fderiv ℝ
                    (fun w : Space =>
                      scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z'
                      (basisVector k))
                  z (basisVector i))
                y (basisVector i)| ≤ E y := by
  obtain ⟨M₁, hM₁₀, hM₁⟩ := standardCutoff_coordinate_derivative_rates.1
  have hM2 : ∀ i j : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
          (basisVector j)| ≤ R⁻¹ * R⁻¹ * M :=
    standardCutoff_coordinate_derivative_rates.2.1
  let M₂ : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hM2 i j)
  have hM₂ : ∀ i j : Fin 3, 0 ≤ M₂ i j ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
          (basisVector j)| ≤ R⁻¹ * R⁻¹ * M₂ i j :=
    fun i j => Classical.choose_spec (hM2 i j)
  have hM3 : ∀ i j k : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R →
      ∀ x : Space,
        |thirdDirectional (scaledCutoff R) (basisVector i) (basisVector j)
            (basisVector k) x| ≤
          R⁻¹ * R⁻¹ * R⁻¹ * M :=
    standardCutoff_coordinate_derivative_rates.2.2
  let M₃ : Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun i j k => Classical.choose (hM3 i j k)
  have hM₃ : ∀ i j k : Fin 3, 0 ≤ M₃ i j k ∧ ∀ {R : ℝ}, 0 < R →
      ∀ x : Space,
        |thirdDirectional (scaledCutoff R) (basisVector i) (basisVector j)
            (basisVector k) x| ≤
          R⁻¹ * R⁻¹ * R⁻¹ * M₃ i j k :=
    fun i j k => Classical.choose_spec (hM3 i j k)
  obtain ⟨C₁, hC₁, hD1⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  obtain ⟨A₂, B₂, hA₂, hB₂, hD2⟩ :=
    exists_abs_second_heatKernel_translate_le_gaussians hκ hτ x₀
  obtain ⟨A₃, B₃, hA₃, hB₃, hD3⟩ :=
    exists_abs_third_heatKernel_translate_le_gaussians hκ hτ x₀
  let M₂sum : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, M₂ i j
  have hM₂sum₀ : 0 ≤ M₂sum :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hM₂ i j).1
  have hM₂le : ∀ i j : Fin 3, M₂ i j ≤ M₂sum := by
    intro i j
    calc M₂ i j ≤ ∑ b : Fin 3, M₂ i b :=
          Finset.single_le_sum (fun b _ => (hM₂ i b).1) (Finset.mem_univ j)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, M₂ a b :=
          Finset.single_le_sum (fun a _ =>
            Finset.sum_nonneg (fun b _ => (hM₂ a b).1)) (Finset.mem_univ i)
  let M₃sum : ℝ := ∑ i : Fin 3, ∑ k : Fin 3, M₃ k i i
  have hM₃sum₀ : 0 ≤ M₃sum :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (hM₃ k i i).1
  have hM₃le : ∀ i k : Fin 3, M₃ k i i ≤ M₃sum := by
    intro i k
    calc M₃ k i i ≤ ∑ a : Fin 3, M₃ k a a :=
          Finset.single_le_sum (fun a _ => (hM₃ k a a).1) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, M₃ b a a :=
          Finset.single_le_sum
            (fun b _ => Finset.sum_nonneg fun a _ => (hM₃ b a a).1)
            (Finset.mem_univ k)
      _ = M₃sum := by exact Finset.sum_comm
  let c₁ : ℝ := M₃sum + 3 * M₁ * B₂
  let c₂ : ℝ := 3 * M₂sum * C₁ + B₃
  let c₃ : ℝ := 3 * M₁ * A₂
  let c₄ : ℝ := A₃
  let E : Space → ℝ := fun y =>
    c₁ * heatKernel κ τ (x₀ - y) + c₂ * heatKernel κ (2 * τ) (x₀ - y) +
      c₃ * heatKernel κ (4 * τ) (x₀ - y) +
        c₄ * heatKernel κ (8 * τ) (x₀ - y)
  have hc₁₀ : 0 ≤ c₁ := by
    show 0 ≤ M₃sum + 3 * M₁ * B₂
    positivity
  have hc₂₀ : 0 ≤ c₂ := by
    show 0 ≤ 3 * M₂sum * C₁ + B₃
    positivity
  have hc₃₀ : 0 ≤ c₃ := by
    show 0 ≤ 3 * M₁ * A₂
    positivity
  refine ⟨E, ?_, ?_, ?_⟩
  · intro y
    have hG0 : 0 ≤ heatKernel κ τ (x₀ - y) := heatKernel_nonneg hκ hτ _
    have hG20 : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hG40 : 0 ≤ heatKernel κ (4 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hG80 : 0 ≤ heatKernel κ (8 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    show 0 ≤ c₁ * heatKernel κ τ (x₀ - y) + c₂ * heatKernel κ (2 * τ) (x₀ - y) +
      c₃ * heatKernel κ (4 * τ) (x₀ - y) + c₄ * heatKernel κ (8 * τ) (x₀ - y)
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg hc₁₀ hG0
    · exact mul_nonneg hc₂₀ hG20
    · exact mul_nonneg hc₃₀ hG40
    · exact mul_nonneg (le_of_lt hA₃) hG80
  · have hg2 : ∀ t : ℝ, 0 < t →
      Integrable (fun y : Space => heatKernel κ t (x₀ - y) ^ 2) := by
      intro t ht
      refine ((integrable_heatKernel_rpow hκ ht
          (by norm_num : (0 : ℝ) < 2)).comp_sub_right x₀).congr ?_
      exact ae_of_all _ fun y => by
        dsimp only
        rw [heatKernel_comm κ t y x₀, Real.rpow_two, pow_two]
    have hsum_int : Integrable (fun y : Space =>
        c₁ ^ 2 * heatKernel κ τ (x₀ - y) ^ 2 +
          (c₂ ^ 2 * heatKernel κ (2 * τ) (x₀ - y) ^ 2 +
            (c₃ ^ 2 * heatKernel κ (4 * τ) (x₀ - y) ^ 2 +
              c₄ ^ 2 * heatKernel κ (8 * τ) (x₀ - y) ^ 2))) := by
      refine ((hg2 τ hτ).const_mul (c₁ ^ 2)).add ?_
      refine ((hg2 (2 * τ) (by positivity)).const_mul (c₂ ^ 2)).add ?_
      refine ((hg2 (4 * τ) (by positivity)).const_mul (c₃ ^ 2)).add ?_
      exact (hg2 (8 * τ) (by positivity)).const_mul (c₄ ^ 2)
    have h1 : ContDiff ℝ ∞ (fun y : Space =>
        c₁ * heatKernel κ τ (x₀ - y)) :=
      contDiff_const.mul (heatKernel_translate_contDiff κ τ x₀)
    have h2 : ContDiff ℝ ∞ (fun y : Space =>
        c₂ * heatKernel κ (2 * τ) (x₀ - y)) :=
      contDiff_const.mul (heatKernel_translate_contDiff κ (2 * τ) x₀)
    have h3 : ContDiff ℝ ∞ (fun y : Space =>
        c₃ * heatKernel κ (4 * τ) (x₀ - y)) :=
      contDiff_const.mul (heatKernel_translate_contDiff κ (4 * τ) x₀)
    have h4 : ContDiff ℝ ∞ (fun y : Space =>
        c₄ * heatKernel κ (8 * τ) (x₀ - y)) :=
      contDiff_const.mul (heatKernel_translate_contDiff κ (8 * τ) x₀)
    have hEcont : Continuous (fun y : Space => E y ^ 2) :=
      (((h1.add h2).add h3).add h4).continuous.pow 2
    refine Integrable.mono' (hsum_int.const_mul 4)
      hEcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine (sq_four_sum_le (c₁ * heatKernel κ τ (x₀ - y))
        (c₂ * heatKernel κ (2 * τ) (x₀ - y))
        (c₃ * heatKernel κ (4 * τ) (x₀ - y))
        (c₄ * heatKernel κ (8 * τ) (x₀ - y))).trans ?_
    exact le_of_eq (by ring)
  · intro R i k y
    obtain ⟨hRinv, hRinv2, hRinv3⟩ := inv_absorb R
    have hR0 : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left 1 R)
    have hGsmooth : ContDiff ℝ ∞ (fun w : Space =>
        heatKernel κ τ (x₀ - w)) := heatKernel_translate_contDiff κ τ x₀
    have hFsmooth : ContDiff ℝ ∞ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) :=
      (scaledCutoff_contDiff (max 1 R)).mul hGsmooth
    have hGτ : 0 ≤ heatKernel κ τ (x₀ - y) := heatKernel_nonneg hκ hτ _
    have hG2τ : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hG4τ : 0 ≤ heatKernel κ (4 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hG8τ : 0 ≤ heatKernel κ (8 * τ) (x₀ - y) :=
      heatKernel_nonneg hκ (by positivity) _
    have hχ1 : ∀ m : Fin 3,
        |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector m)| ≤ M₁ := by
      intro m
      calc |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector m)|
          ≤ (max 1 R)⁻¹ * M₁ := hM₁ (R := max 1 R) hR0 y m
        _ ≤ 1 * M₁ := mul_le_mul_of_nonneg_right hRinv hM₁₀
        _ = M₁ := one_mul _
    have hχ2 : ∀ a b : Fin 3,
        |fderiv ℝ (fun z : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector a)) y
            (basisVector b)| ≤ M₂ a b := by
      intro a b
      calc |fderiv ℝ (fun z : Space =>
              fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector a)) y
              (basisVector b)|
          ≤ (max 1 R)⁻¹ * (max 1 R)⁻¹ * M₂ a b :=
            (hM₂ a b).2 (R := max 1 R) hR0 y
        _ ≤ M₂ a b := by
          rw [show (max 1 R)⁻¹ * (max 1 R)⁻¹ * M₂ a b =
                ((max 1 R)⁻¹ * (max 1 R)⁻¹) * M₂ a b by ring]
          refine (mul_le_mul_of_nonneg_right hRinv2 (hM₂ a b).1).trans ?_
          simp
    have hχ3 : ∀ a b c : Fin 3,
        |fderiv ℝ (fun r : Space => fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff (max 1 R)) z
              (basisVector a)) r (basisVector b)) y (basisVector c)| ≤
          M₃ a b c := by
      intro a b c
      calc |fderiv ℝ (fun r : Space => fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff (max 1 R)) z
                (basisVector a)) r (basisVector b)) y (basisVector c)|
          ≤ (max 1 R)⁻¹ * (max 1 R)⁻¹ * (max 1 R)⁻¹ * M₃ a b c :=
            (hM₃ a b c).2 (R := max 1 R) hR0 y
        _ ≤ M₃ a b c := by
          refine (mul_le_mul_of_nonneg_right hRinv3 (hM₃ a b c).1).trans ?_
          simp
    have hG1 : ∀ m : Fin 3,
        |fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
            (basisVector m)| ≤ C₁ * heatKernel κ (2 * τ) (x₀ - y) := by
      intro m
      have := hD1 x₀ y (basisVector m)
      rw [norm_basisVector] at this
      simpa using this
    have hG2 : ∀ a b : Fin 3,
        |fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => heatKernel κ τ (x₀ - w)) z (basisVector a)) y
            (basisVector b)| ≤
          A₂ * heatKernel κ (4 * τ) (x₀ - y) +
            B₂ * heatKernel κ τ (x₀ - y) :=
      fun a b => hD2 y a b
    have hG3 : ∀ a b c : Fin 3,
        |fderiv ℝ (fun z : Space => fderiv ℝ
            (fun z' : Space => fderiv ℝ
              (fun w : Space => heatKernel κ τ (x₀ - w)) z'
                (basisVector a)) z (basisVector b)) y (basisVector c)| ≤
          A₃ * heatKernel κ (8 * τ) (x₀ - y) +
            B₃ * heatKernel κ (2 * τ) (x₀ - y) :=
      fun a b c => hD3 y a b c
    -- Expand `D_k (χ · G)` by the product rule, then split the second
    -- derivative across the two summands.
    have hDkχ : ContDiff ℝ ∞ (fun z : Space =>
        fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector k)) :=
      contDiff_fderiv_apply (scaledCutoff_contDiff (max 1 R))
        (basisVector k)
    have hDkG : ContDiff ℝ ∞ (fun z : Space =>
        fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
          (basisVector k)) :=
      contDiff_fderiv_apply hGsmooth (basisVector k)
    have hfirstfun :
        (fun z' : Space => fderiv ℝ
            (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z'
              (basisVector k)) =
          fun z' : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z' (basisVector k) *
              heatKernel κ τ (x₀ - z') +
              scaledCutoff (max 1 R) z' *
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z'
                  (basisVector k) := by
      funext z'
      rw [firstDirectional_mul (scaledCutoff_contDiff (max 1 R)) hGsmooth k z']
    rw [hfirstfun]
    rw [secondDirectional_add (hDkχ.mul hGsmooth)
      ((scaledCutoff_contDiff (max 1 R)).mul hDkG) i y]
    have hslot1 : |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z' (basisVector k) *
              heatKernel κ τ (x₀ - z')) z (basisVector i)) y
          (basisVector i)| ≤
        (M₃sum + M₁ * B₂) * heatKernel κ τ (x₀ - y) +
          (2 * M₂sum * C₁) * heatKernel κ (2 * τ) (x₀ - y) +
            (M₁ * A₂) * heatKernel κ (4 * τ) (x₀ - y) := by
      rw [secondDirectional_mul hDkχ hGsmooth i y]
      have ht1 : |fderiv ℝ (fun z : Space => fderiv ℝ
            (fun z' : Space => fderiv ℝ (scaledCutoff (max 1 R)) z'
              (basisVector k)) z (basisVector i)) y (basisVector i) *
          heatKernel κ τ (x₀ - y)| ≤ M₃sum * heatKernel κ τ (x₀ - y) := by
        rw [abs_mul, abs_of_nonneg hGτ]
        exact mul_le_mul ((hχ3 k i i).trans (hM₃le i k)) (le_refl _) hGτ
          hM₃sum₀
      have ht2 : |2 * (fderiv ℝ (fun z : Space =>
            fderiv ℝ (scaledCutoff (max 1 R)) z (basisVector k)) y
              (basisVector i) *
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
              (basisVector i))| ≤
          (2 * M₂sum * C₁) * heatKernel κ (2 * τ) (x₀ - y) := by
        have hmul : ∀ p q : ℝ, |2 * (p * q)| = 2 * (|p| * |q|) := by
          intro p q
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [hmul]
        have hmid :
            |fderiv ℝ (fun z : Space => fderiv ℝ (scaledCutoff (max 1 R)) z
                (basisVector k)) y (basisVector i)| *
                |fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
                    (basisVector i)| ≤
              M₂sum * (C₁ * heatKernel κ (2 * τ) (x₀ - y)) :=
          (mul_le_mul (hχ2 k i) (hG1 i) (abs_nonneg _) (hM₂ k i).1).trans
            (mul_le_mul_of_nonneg_right (hM₂le k i)
              (mul_nonneg (le_of_lt hC₁) hG2τ))
        exact (mul_le_mul_of_nonneg_left hmid
          (by norm_num : (0 : ℝ) ≤ 2)).trans (le_of_eq (by ring))
      have ht3 : |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector k) *
          fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => heatKernel κ τ (x₀ - w)) z (basisVector i)) y
            (basisVector i)| ≤
          (M₁ * A₂) * heatKernel κ (4 * τ) (x₀ - y) +
            (M₁ * B₂) * heatKernel κ τ (x₀ - y) := by
        rw [abs_mul]
        exact (mul_le_mul (hχ1 k) (hG2 i i) (abs_nonneg _) hM₁₀).trans
          (le_of_eq (by ring))
      refine ((abs_sum_three_le _ _ _).trans
          (add_le_add (add_le_add ht1 ht2) ht3)).trans ?_
      exact le_of_eq (by ring)
    have hslot2 : |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space =>
            scaledCutoff (max 1 R) z' *
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z'
                (basisVector k)) z (basisVector i)) y (basisVector i)| ≤
        (M₂sum * C₁) * heatKernel κ (2 * τ) (x₀ - y) +
          ((2 * M₁ * A₂) * heatKernel κ (4 * τ) (x₀ - y) +
            (2 * M₁ * B₂) * heatKernel κ τ (x₀ - y)) +
              (A₃ * heatKernel κ (8 * τ) (x₀ - y) +
                B₃ * heatKernel κ (2 * τ) (x₀ - y)) := by
      rw [secondDirectional_mul (scaledCutoff_contDiff (max 1 R)) hDkG i y]
      have hq1 : |fderiv ℝ (fun z : Space => fderiv ℝ
            (scaledCutoff (max 1 R)) z (basisVector i)) y (basisVector i) *
          fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) y
            (basisVector k)| ≤
          (M₂sum * C₁) * heatKernel κ (2 * τ) (x₀ - y) := by
        rw [abs_mul]
        refine ((mul_le_mul (hχ2 i i) (hG1 k) (abs_nonneg _) (hM₂ i i).1).trans
          (mul_le_mul_of_nonneg_right (hM₂le i i)
            (mul_nonneg (le_of_lt hC₁) hG2τ))).trans ?_
        exact le_of_eq (by ring)
      have hq2 : |2 * (fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector i) *
            fderiv ℝ (fun z : Space => fderiv ℝ
              (fun w : Space => heatKernel κ τ (x₀ - w)) z (basisVector k)) y
              (basisVector i))| ≤
          (2 * M₁ * A₂) * heatKernel κ (4 * τ) (x₀ - y) +
            (2 * M₁ * B₂) * heatKernel κ τ (x₀ - y) := by
        have hmul : ∀ p q : ℝ, |2 * (p * q)| = 2 * (|p| * |q|) := by
          intro p q
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [hmul]
        have hmid :
            |fderiv ℝ (scaledCutoff (max 1 R)) y (basisVector i)| *
              |fderiv ℝ (fun z : Space => fderiv ℝ
                  (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector k)) y (basisVector i)| ≤
            (M₁ * A₂) * heatKernel κ (4 * τ) (x₀ - y) +
              (M₁ * B₂) * heatKernel κ τ (x₀ - y) :=
          (mul_le_mul (hχ1 i) (hG2 k i) (abs_nonneg _) hM₁₀).trans
            (le_of_eq (by ring))
        exact (mul_le_mul_of_nonneg_left hmid
          (by norm_num : (0 : ℝ) ≤ 2)).trans (le_of_eq (by ring))
      have hq3 : |scaledCutoff (max 1 R) y * fderiv ℝ
            (fun z : Space => fderiv ℝ
              (fun z' : Space => fderiv ℝ
                (fun w : Space => heatKernel κ τ (x₀ - w)) z'
                  (basisVector k)) z (basisVector i)) y (basisVector i)| ≤
          A₃ * heatKernel κ (8 * τ) (x₀ - y) +
            B₃ * heatKernel κ (2 * τ) (x₀ - y) := by
        rw [abs_mul, abs_of_nonneg (scaledCutoff_nonneg (max 1 R) y)]
        exact (mul_le_mul (scaledCutoff_le_one _ _) (hG3 k i i)
          (abs_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
      refine ((abs_sum_three_le _ _ _).trans
          (add_le_add (add_le_add hq1 hq2) hq3)).trans ?_
      exact le_of_eq (by ring)
    refine ((abs_add_le _ _).trans (add_le_add hslot1 hslot2)).trans ?_
    refine le_of_eq ?_
    unfold E c₁ c₂ c₃ c₄
    ring

/-! ### Coordinate formulas for the exact compact test

Copied from the private lemmas of
`WholeSpaceSolenoidalHeatConvectionLimit`: the radius-total test `curl
(χ_{max 1 R} G_τ(x₀ − ·) · a)` expands coordinatewise into first
directional derivatives of the scalar cutoff Gaussian. -/

private theorem atTopCompactBackwardHeatCurlTest_component_zero
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 0) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 1) * a 2 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 2) * a 1 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 0 = _
  have hfun : (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) := by
    funext z
    rw [smul_smul]
  rw [hfun]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem atTopCompactBackwardHeatCurlTest_component_one
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 1) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 2) * a 0 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 0) * a 2 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 1 = _
  have hfun : (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) := by
    funext z
    rw [smul_smul]
  rw [hfun]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem atTopCompactBackwardHeatCurlTest_component_two
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 2) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 0) * a 1 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 1) * a 0 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 2 = _
  have hfun : (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) := by
    funext z
    rw [smul_smul]
  rw [hfun]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem atTopTest_DcontDiff (κ τ : ℝ) (x₀ : Space) (R : ℝ) (m : Fin 3) :
    ContDiff ℝ ∞ (fun z : Space => fderiv ℝ
      (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
      z (basisVector m)) :=
  contDiff_fderiv_apply
    ((scaledCutoff_contDiff (max 1 R)).mul (heatKernel_translate_contDiff κ τ x₀))
    (basisVector m)

/-- First directional derivative of each coordinate of the exact compact test,
expanded through the component formulas. -/
private theorem atTopTest_first_deriv_zero
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (y v : Space) :
    fderiv ℝ (fun z : Space =>
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 0) y v =
      a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
        z (basisVector 1)) y v -
        a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
          z (basisVector 2)) y v := by
  have hin : (fun z : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 0) =
      fun z : Space =>
        a 2 • fderiv ℝ (fun w : Space =>
          scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 1) -
          a 1 • fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 2) := by
    rw [atTopCompactBackwardHeatCurlTest_component_zero]
    refine funext (fun z => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  rw [firstDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 1)
    (atTopTest_DcontDiff κ τ x₀ R 2) (a 2) (a 1) v y]

private theorem atTopTest_first_deriv_one
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (y v : Space) :
    fderiv ℝ (fun z : Space =>
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 1) y v =
      a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
        z (basisVector 2)) y v -
        a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
          z (basisVector 0)) y v := by
  have hin : (fun z : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 1) =
      fun z : Space =>
        a 0 • fderiv ℝ (fun w : Space =>
          scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 2) -
          a 2 • fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 0) := by
    rw [atTopCompactBackwardHeatCurlTest_component_one]
    refine funext (fun z => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  rw [firstDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 2)
    (atTopTest_DcontDiff κ τ x₀ R 0) (a 0) (a 2) v y]

private theorem atTopTest_first_deriv_two
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (y v : Space) :
    fderiv ℝ (fun z : Space =>
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 2) y v =
      a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
        z (basisVector 0)) y v -
        a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
          z (basisVector 1)) y v := by
  have hin : (fun z : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 2) =
      fun z : Space =>
        a 1 • fderiv ℝ (fun w : Space =>
          scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 0) -
          a 0 • fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z (basisVector 1) := by
    rw [atTopCompactBackwardHeatCurlTest_component_two]
    refine funext (fun z => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  rw [firstDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 0)
    (atTopTest_DcontDiff κ τ x₀ R 1) (a 1) (a 0) v y]

/-- Diagonal second directional derivative of each coordinate of the exact
compact test, expanded through the component formulas. -/
private theorem atTopTest_second_deriv_zero
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (i : Fin 3) (y : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 0)
        z (basisVector i)) y (basisVector i) =
      a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 1)) z (basisVector i)) y (basisVector i) -
        a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 2)) z (basisVector i)) y (basisVector i) := by
  have hin : (fun w : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 0) =
      fun w : Space =>
        a 2 • fderiv ℝ (fun v : Space =>
          scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 1) -
          a 1 • fderiv ℝ (fun v : Space =>
            scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 2) := by
    rw [atTopCompactBackwardHeatCurlTest_component_zero]
    refine funext (fun w => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  exact secondDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 1)
    (atTopTest_DcontDiff κ τ x₀ R 2) (a 2) (a 1) i y

private theorem atTopTest_second_deriv_one
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (i : Fin 3) (y : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 1)
        z (basisVector i)) y (basisVector i) =
      a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 2)) z (basisVector i)) y (basisVector i) -
        a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 0)) z (basisVector i)) y (basisVector i) := by
  have hin : (fun w : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 1) =
      fun w : Space =>
        a 0 • fderiv ℝ (fun v : Space =>
          scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 2) -
          a 2 • fderiv ℝ (fun v : Space =>
            scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 0) := by
    rw [atTopCompactBackwardHeatCurlTest_component_one]
    refine funext (fun w => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  exact secondDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 2)
    (atTopTest_DcontDiff κ τ x₀ R 0) (a 0) (a 2) i y

private theorem atTopTest_second_deriv_two
    (κ τ : ℝ) (x₀ a : Space) (R : ℝ) (i : Fin 3) (y : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 2)
        z (basisVector i)) y (basisVector i) =
      a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 0)) z (basisVector i)) y (basisVector i) -
        a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
          (fun z' : Space => fderiv ℝ
            (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
            z' (basisVector 1)) z (basisVector i)) y (basisVector i) := by
  have hin : (fun w : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 2) =
      fun w : Space =>
        a 1 • fderiv ℝ (fun v : Space =>
          scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 0) -
          a 0 • fderiv ℝ (fun v : Space =>
            scaledCutoff (max 1 R) v * heatKernel κ τ (x₀ - v)) w (basisVector 1) := by
    rw [atTopCompactBackwardHeatCurlTest_component_two]
    refine funext (fun w => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hin]
  exact secondDirectional_sub_smul (atTopTest_DcontDiff κ τ x₀ R 0)
    (atTopTest_DcontDiff κ τ x₀ R 1) (a 1) (a 0) i y

/-! ## B4: the radius- and time-uniform majorant for the fixed-time RHS -/

/-- **Radius- and time-uniform bound for the compact-test weak RHS.**  For
the exact pressure-free right-hand side `lerayWeakRhs ν (atTopCompact
BackwardHeatCurlTest R κ τ x₀ a) u s`, every radius `R` and every time slice
`s ∈ [0, T)` is dominated by one constant independent of both.  The convection
slots are absorbed by the uniform second-derivative envelope
`exists_D2_scaledCutoff_heatKernel_uniform_bound` and the energy bound
`energy_le_initial`; the viscous slots by the Gaussian third-derivative
envelope `exists_D3_scaledCutoff_heatKernel_envelope` and Young's inequality
`2 a b ≤ a² + b²`.  The envelope itself is radius-free, so no time-uniform
continuity of the solution is consumed. -/
theorem SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (_hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ (R : ℝ) {s : ℝ}, 0 ≤ s → s < T →
      |lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s| ≤ W := by
  obtain ⟨K₂, hK₂₀, hK₂⟩ :=
    exists_D2_scaledCutoff_heatKernel_uniform_bound hκ hτ x₀
  obtain ⟨E, hEnonneg, hEint, hE⟩ :=
    exists_D3_scaledCutoff_heatKernel_envelope hκ hτ x₀
  let S := |a 0| + |a 1| + |a 2|
  have hSdef : S = |a 0| + |a 1| + |a 2| := rfl
  have hS₀ : 0 ≤ S := by
    nlinarith [hSdef, abs_nonneg (a 0), abs_nonneg (a 1),
      abs_nonneg (a 2)]
  have ha_le : ∀ i : Fin 3, |a i| ≤ S := by
    intro i
    fin_cases i
    · show |a 0| ≤ S
      nlinarith [hSdef, abs_nonneg (a 1), abs_nonneg (a 2)]
    · show |a 1| ≤ S
      nlinarith [hSdef, abs_nonneg (a 0), abs_nonneg (a 2)]
    · show |a 2| ≤ S
      nlinarith [hSdef, abs_nonneg (a 0), abs_nonneg (a 1)]
  let E₀ := kineticEnergy u 0
  have hE₀₀ : 0 ≤ E₀ := by
    show 0 ≤ kineticEnergy u 0
    unfold kineticEnergy
    exact integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
  let IE := ∫ y : Space, E y ^ 2
  have hIE₀ : 0 ≤ IE := by
    show 0 ≤ ∫ y : Space, E y ^ 2
    exact integral_nonneg fun y => sq_nonneg (E y)
  let W := 18 * S * K₂ * E₀ + |ν| * (9 * S * (IE + E₀))
  have hW₀ : 0 ≤ W := by
    have h1 : 0 ≤ 18 * S * K₂ * E₀ :=
      mul_nonneg (mul_nonneg (mul_nonneg
        (by norm_num : (0 : ℝ) ≤ 18) hS₀) hK₂₀) hE₀₀
    have h2 : 0 ≤ |ν| * (9 * S * (IE + E₀)) :=
      mul_nonneg (abs_nonneg ν)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hS₀)
          (add_nonneg hIE₀ hE₀₀))
    exact add_nonneg h1 h2
  refine ⟨W, hW₀, ?_⟩
  intro R s hs0 hsT
  have hus : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hfin : Integrable (fun y : Space => ‖u s y‖ ^ 2) :=
    hsol.finite_energy s hs0 hsT
  have hEs : ∫ y : Space, ‖u s y‖ ^ 2 ≤ E₀ :=
    SolvesBefore.integral_supNorm_sq_le hsol hs0 hsT
  have hDslot : ∀ (R : ℝ) (m : Fin 3) (y v : Space),
      |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
          z (basisVector m)) y v| ≤
        3 * K₂ * ‖v‖ := by
    intro R m y v
    exact clm_apply_bound _ (fun i => hK₂ R i m y)
  -- convection slots, pointwise
  have hconvPoint : ∀ (R : ℝ) (j : Fin 3) (y : Space),
      |fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z j) y (u s y) *
          u s y j| ≤
        6 * S * K₂ * ‖u s y‖ ^ 2 := by
    intro R j y
    fin_cases j
    · show |(fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 0) y (u s y)) *
          u s y 0| ≤ 6 * S * K₂ * ‖u s y‖ ^ 2
      rw [atTopTest_first_deriv_zero κ τ x₀ a R y (u s y), abs_mul]
      have hsub :
          |a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
              z (basisVector 1)) y (u s y) -
              a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z (basisVector 2)) y (u s y)| ≤
            6 * S * K₂ * ‖u s y‖ := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 2) (hDslot R 1 y (u s y)) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 1) (hDslot R 2 y (u s y)) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 0) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hS₀)
            hK₂₀) (norm_nonneg _))).trans (le_of_eq (by ring))
    · show |(fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 1) y (u s y)) *
          u s y 1| ≤ 6 * S * K₂ * ‖u s y‖ ^ 2
      rw [atTopTest_first_deriv_one κ τ x₀ a R y (u s y), abs_mul]
      have hsub :
          |a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
              z (basisVector 2)) y (u s y) -
              a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z (basisVector 0)) y (u s y)| ≤
            6 * S * K₂ * ‖u s y‖ := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 0) (hDslot R 2 y (u s y)) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 2) (hDslot R 0 y (u s y)) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 1) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hS₀)
            hK₂₀) (norm_nonneg _))).trans (le_of_eq (by ring))
    · show |(fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 2) y (u s y)) *
          u s y 2| ≤ 6 * S * K₂ * ‖u s y‖ ^ 2
      rw [atTopTest_first_deriv_two κ τ x₀ a R y (u s y), abs_mul]
      have hsub :
          |a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
              z (basisVector 0)) y (u s y) -
              a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z (basisVector 1)) y (u s y)| ≤
            6 * S * K₂ * ‖u s y‖ := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 1) (hDslot R 0 y (u s y)) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 0) (hDslot R 1 y (u s y)) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 2) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hS₀)
            hK₂₀) (norm_nonneg _))).trans (le_of_eq (by ring))

  have hconvSlot : ∀ (R : ℝ) (j : Fin 3),
      |∫ y : Space, fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z j) y (u s y) *
          u s y j| ≤
        6 * S * K₂ * E₀ := by
    intro R j
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
        (hfin.const_mul (6 * S * K₂))
        (ae_of_all _ fun y => hconvPoint R j y)).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hEs
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hS₀) hK₂₀)
  -- viscous slots, pointwise
  have hviscPoint : ∀ (R : ℝ) (i j : Fin 3) (y : Space),
      |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w j)
          z (basisVector i)) y (basisVector i) * u s y j| ≤
        S * (E y ^ 2 + ‖u s y‖ ^ 2) := by
    intro R i j y
    fin_cases j
    · show |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 0)
          z (basisVector i)) y (basisVector i) * u s y 0| ≤
        S * (E y ^ 2 + ‖u s y‖ ^ 2)
      rw [atTopTest_second_deriv_zero κ τ x₀ a R i y, abs_mul]
      have hsub :
          |a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun z' : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z' (basisVector 1)) z (basisVector i)) y (basisVector i) -
              a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun z' : Space => fderiv ℝ
                  (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                  z' (basisVector 2)) z (basisVector i)) y (basisVector i)| ≤
            2 * S * E y := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 2) (hE R i 1 y) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 1) (hE R i 2 y) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      have ham : 2 * E y * ‖u s y‖ ≤ E y ^ 2 + ‖u s y‖ ^ 2 := by
        nlinarith [sq_nonneg (E y - ‖u s y‖)]
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 0) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS₀) (hEnonneg y))).trans
          ((Eq.le (by ring :
              (2 * S * E y) * ‖u s y‖ = S * (2 * E y * ‖u s y‖))).trans
            (mul_le_mul_of_nonneg_left ham hS₀))
    · show |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 1)
          z (basisVector i)) y (basisVector i) * u s y 1| ≤
        S * (E y ^ 2 + ‖u s y‖ ^ 2)
      rw [atTopTest_second_deriv_one κ τ x₀ a R i y, abs_mul]
      have hsub :
          |a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun z' : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z' (basisVector 2)) z (basisVector i)) y (basisVector i) -
              a 2 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun z' : Space => fderiv ℝ
                  (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                  z' (basisVector 0)) z (basisVector i)) y (basisVector i)| ≤
            2 * S * E y := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 0) (hE R i 2 y) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 2) (hE R i 0 y) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      have ham : 2 * E y * ‖u s y‖ ≤ E y ^ 2 + ‖u s y‖ ^ 2 := by
        nlinarith [sq_nonneg (E y - ‖u s y‖)]
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 1) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS₀) (hEnonneg y))).trans
          ((Eq.le (by ring :
              (2 * S * E y) * ‖u s y‖ = S * (2 * E y * ‖u s y‖))).trans
            (mul_le_mul_of_nonneg_left ham hS₀))
    · show |fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w 2)
          z (basisVector i)) y (basisVector i) * u s y 2| ≤
        S * (E y ^ 2 + ‖u s y‖ ^ 2)
      rw [atTopTest_second_deriv_two κ τ x₀ a R i y, abs_mul]
      have hsub :
          |a 1 * fderiv ℝ (fun z : Space => fderiv ℝ
              (fun z' : Space => fderiv ℝ
                (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                z' (basisVector 0)) z (basisVector i)) y (basisVector i) -
              a 0 * fderiv ℝ (fun z : Space => fderiv ℝ
                (fun z' : Space => fderiv ℝ
                  (fun w : Space => scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w))
                  z' (basisVector 1)) z (basisVector i)) y (basisVector i)| ≤
            2 * S * E y := by
        refine ((abs_sub _ _).trans
            (add_le_add
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 1) (hE R i 0 y) (abs_nonneg _) hS₀))
              ((le_of_eq (abs_mul _ _)).trans
                (mul_le_mul (ha_le 0) (hE R i 1 y) (abs_nonneg _) hS₀)))).trans
            (le_of_eq (by ring))
      have ham : 2 * E y * ‖u s y‖ ≤ E y ^ 2 + ‖u s y‖ ^ 2 := by
        nlinarith [sq_nonneg (E y - ‖u s y‖)]
      refine (mul_le_mul hsub (norm_le_pi_norm (u s y) 2) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS₀) (hEnonneg y))).trans
          ((Eq.le (by ring :
              (2 * S * E y) * ‖u s y‖ = S * (2 * E y * ‖u s y‖))).trans
            (mul_le_mul_of_nonneg_left ham hS₀))

  have hviscSlot : ∀ (R : ℝ) (i j : Fin 3),
      |∫ y : Space, fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w j)
          z (basisVector i)) y (basisVector i) * u s y j| ≤
        S * (IE + E₀) := by
    intro R i j
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
        ((hEint.add hfin).const_mul S)
        (ae_of_all _ fun y => hviscPoint R i j y)).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hS₀
    simp only [Pi.add_apply]
    rw [integral_add hEint hfin]
    exact add_le_add (le_refl _) hEs
  -- assemble
  have hsum1 : (∑ j : Fin 3, (6 : ℝ) * S * K₂ * E₀) =
      18 * S * K₂ * E₀ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hsum2 : (∑ j : Fin 3, ∑ i : Fin 3, S * (IE + E₀)) =
      9 * S * (IE + E₀) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [lerayWeakRhs_compactBackwardHeatCurlTest_eq hsol hs0 hsT R κ τ x₀ a]
  have hconvSum :
      |∑ j : Fin 3, ∫ y : Space, fderiv ℝ (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z j) y (u s y) *
          u s y j| ≤
        18 * S * K₂ * E₀ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => hconvSlot R j).trans ?_)
    exact le_of_eq hsum1
  have hviscSum :
      |∑ j : Fin 3, ∑ i : Fin 3, ∫ y : Space, fderiv ℝ (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w j)
          z (basisVector i)) y (basisVector i) * u s y j| ≤
        9 * S * (IE + E₀) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => hviscSlot R i j)).trans ?_)
    exact le_of_eq hsum2
  exact (abs_add_le _ _).trans
    (add_le_add hconvSum
      ((Eq.le (abs_mul ν _)).trans
        (mul_le_mul_of_nonneg_left hviscSum (abs_nonneg ν))))

/-! ## Part C: time-continuity of the fixed-radius slot -/

/-- **The exact compact-test slot is continuous in time on every closed
interior interval.**  For each fixed radius `R` the function
`s ↦ lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s` is
continuous on `[ta, tb] ⊆ (0, T)`.  The proof reuses the repository's own
differentiation-under-the-integral mechanism: the coordinate three-slot
pairing equals the time-derivative integral
(`cutoff_testedMomentum_coordinate`), which is continuous on the interval
(`cutoffTimeDerivative_continuousOn`), and the pressure slots cancel in the
coordinate sum pointwise (`pressurePairing_sum_eq_zero`). -/
theorem SolvesBefore.continuousOn_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {ta tb : ℝ} (hta0 : 0 < ta) (_htab : ta ≤ tb) (htbT : tb < T)
    (R κ τ : ℝ) (x₀ a : Space) :
    ContinuousOn (fun t : ℝ => lerayWeakRhs ν
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t) (Set.Icc ta tb) := by
  let sol : PartialClassicalSolution ν zeroForce (u 0) T :=
    { terminalTime_pos := hT
      velocity := u
      pressure := p
      velocity_smooth := hsol.classical.1
      pressure_smooth := hsol.classical.2.1
      initial_condition := rfl
      incompressible := hsol.classical.2.2.1
      equation := hsol.classical.2.2.2 }
  let φ : CompactSolenoidalTest :=
    atTopCompactBackwardHeatCurlTest R κ τ x₀ a
  have hpSmooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ ∞ (sol.pressure t) := by
    intro t ht
    exact ParabolicCaccioppoli.pressure_slice_contDiff sol
      (hta0.le.trans ht.1) (ht.2.trans_lt htbT)
  have hfullContinuous : ∀ j : Fin 3, ContinuousOn (fun t : ℝ =>
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x)) (Set.Icc ta tb) := by
    intro j
    have hleft := cutoffTimeDerivative_continuousOn sol (φ.smooth j)
      (φ.compact j) hta0 htbT j
    refine hleft.congr ?_
    intro t ht
    exact (WholeSpaceDuhamel.cutoff_testedMomentum_coordinate sol
      (φ.smooth j) (φ.compact j) (hta0.le.trans ht.1) (ht.2.trans_lt htbT) j).symm
  have hcont3 : ContinuousOn (fun t : ℝ =>
          ∑ j : Fin 3,
          ((∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x))) (Set.Icc ta tb) :=
    continuousOn_finsetSum Finset.univ fun j _ => hfullContinuous j
  refine hcont3.congr fun t ht => ?_
  rw [show lerayWeakRhs ν φ u t =
        ∑ j : Fin 3,
          ((∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j))
      from rfl]
  show ∑ j : Fin 3,
          ((∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j)) =
      ∑ j : Fin 3,
          ((∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (sol.velocity t x) *
              sol.velocity t x j) +
          ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ
              (fun z => fderiv ℝ (fun y => φ.field y j) z (basisVector i)) x
              (basisVector i)) * sol.velocity t x j) +
          (∫ x : Space,
            fderiv ℝ (fun y => φ.field y j) x (basisVector j) *
              sol.pressure t x))
  conv_rhs => rw [Finset.sum_add_distrib]
  rw [pressurePairing_sum_eq_zero φ (sol.pressure t) (hpSmooth t ht)]
  rw [add_zero]

/-! ## Part D: dominated convergence and the limit of the interval integrals -/

/-- **The limit of the exact interval integrals is the interval integral of
the pointwise limit.**  The `R`-uniform majorant of Part B4 dominates the
slot family on `volume.restrict (uIoc ta tb)`; the fixed-time pointwise
limit is `SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs`;
measurability at each radius is Part C.  This is the time-uniformity
identification whose absence was recorded in
`WholeSpaceSolenoidalHeatIntegratedRhsLimit`. -/
theorem SolvesBefore.tendsto_intervalIntegral_atTopCompactBackwardHeatCurlTest_lerayWeakRhs
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {ta tb : ℝ} (hta0 : 0 < ta) (htab : ta ≤ tb) (htbT : tb < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (fun R : ℝ => ∫ s in ta..tb,
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s)
      atTop (nhds (∫ s in ta..tb, backwardHeatCurlRhs ν κ τ x₀ a u s)) := by
  obtain ⟨W, _hW₀, hW⟩ :=
    SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
      hT hsol hκ hτ x₀ a
  have hF_meas : ∀ᶠ R in atTop, AEStronglyMeasurable
      (fun s : ℝ => lerayWeakRhs ν
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s)
      (volume.restrict (uIoc ta tb)) := by
    filter_upwards with R
    have hcont :=
      SolvesBefore.continuousOn_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
        hT hsol hta0 htab htbT R κ τ x₀ a
    refine (hcont.mono ?_).aestronglyMeasurable measurableSet_uIoc
    rw [uIoc_of_le htab]
    exact Ioc_subset_Icc_self
  have h_bound : ∀ᶠ R in atTop, ∀ᵐ s ∂volume.restrict (uIoc ta tb),
      ‖lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s‖ ≤ W := by
    filter_upwards with R
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le htab] at hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Real.norm_eq_abs]
    exact hW R (by linarith) (by linarith)
  have hWint : Integrable (fun _ : ℝ => W) (volume.restrict (uIoc ta tb)) := by
    haveI : IsFiniteMeasure (volume.restrict (uIoc ta tb)) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    exact integrable_const W
  have h_lim : ∀ᵐ s ∂volume.restrict (uIoc ta tb), Tendsto
      (fun R : ℝ => lerayWeakRhs ν
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s)
      atTop (nhds (backwardHeatCurlRhs ν κ τ x₀ a u s)) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le htab] at hs
    obtain ⟨hs1, hs2⟩ := hs
    exact SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs
      hsol (by linarith) (by linarith) hκ hτ x₀ a
  have hDCT := tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => W) hF_meas h_bound hWint h_lim
  have hL : (fun R : ℝ => ∫ s in ta..tb,
        lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s) =
      (fun R : ℝ => ∫ s : ℝ, lerayWeakRhs ν
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s
          ∂(volume.restrict (uIoc ta tb))) := by
    funext R
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc _ ta tb volume, if_pos htab, one_smul]
  have hR : (∫ s : ℝ, backwardHeatCurlRhs ν κ τ x₀ a u s
        ∂(volume.restrict (uIoc ta tb))) =
      ∫ s in ta..tb, backwardHeatCurlRhs ν κ τ x₀ a u s := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc _ ta tb volume, if_pos htab, one_smul]
  rw [← hL, hR] at hDCT
  exact hDCT

/-! ## Crown: interval integral of the cutoff-free RHS = endpoint momentum -/

/-- **Interval identification (the last whole-space time-uniformity
obligation).**  The interval integral of the cutoff-free right-hand side
`backwardHeatCurlRhs ν κ τ x₀ a u` over `[ta, tb] ⊂ (0, T)` equals the
endpoint momentum difference of the uncut backward-heat-curl momentum.  The
limit `fun R => ∫ s in ta..tb, lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest
R κ τ x₀ a) u s` has two closed forms: the interval integral of the
pointwise limit (Part D dominated convergence) and the Gaussian endpoint
momentum difference (`WholeSpaceSolenoidalHeatIntegratedRhsLimit`);
Hausdorff uniqueness identifies them. -/
theorem SolvesBefore.intervalIntegral_backwardHeatCurlRhs_eq_momentumDiff
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {ta tb : ℝ} (hta0 : 0 < ta) (htab : ta ≤ tb) (htbT : tb < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∫ s in ta..tb, backwardHeatCurlRhs ν κ τ x₀ a u s =
      backwardHeatCurlMomentum κ τ x₀ a u tb -
        backwardHeatCurlMomentum κ τ x₀ a u ta :=
  tendsto_nhds_unique
    (SolvesBefore.tendsto_intervalIntegral_atTopCompactBackwardHeatCurlTest_lerayWeakRhs
      hT hsol hta0 htab htbT hκ hτ x₀ a)
    (Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit.SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_lerayWeakRhs
      hT hsol hta0 htab htbT hκ hτ x₀ a)

end Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification.SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification.SolvesBefore.continuousOn_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification.SolvesBefore.tendsto_intervalIntegral_atTopCompactBackwardHeatCurlTest_lerayWeakRhs
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification.SolvesBefore.intervalIntegral_backwardHeatCurlRhs_eq_momentumDiff
