import Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

/-!
# Third spatial derivatives of the whole-space heat kernel

The viscous slot of the pressure-free whole-space evolution tests the
Laplacian of `curl (χ_R G a)`.  Since the curl already differentiates the
potential once, its cutoff-free limit contains third spatial derivatives of
the Gaussian.  This file computes those derivatives and provides the
Gaussian envelope needed to pair them with a finite-energy velocity slice.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators ENNReal NNReal Topology ContDiff Matrix
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceHeatThirdDerivative

open Navier
open Navier.Analysis
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.CurlIdentities
open Navier.Analysis.Vorticity
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

private noncomputable def heatSpatialCoefficient (ν t : ℝ) : ℝ :=
  -(4 * ν * t)⁻¹ * 2

/-- The mixed second spatial coordinate derivative of the heat kernel. -/
theorem fderiv_fderiv_heatKernel_space_apply_mixed
    (ν t : ℝ) (i j : Fin 3) (x : Space) :
    fderiv ℝ
        (fun y : Space =>
          fderiv ℝ (fun z : Space => heatKernel ν t z) y (basisVector i))
        x (basisVector j) =
      heatKernel ν t x *
        (heatSpatialCoefficient ν t * x j *
            (heatSpatialCoefficient ν t * x i) +
          heatSpatialCoefficient ν t * (basisVector j i)) := by
  let c : ℝ := heatSpatialCoefficient ν t
  have hrewrite :
      (fun y : Space =>
          fderiv ℝ (fun z : Space => heatKernel ν t z) y (basisVector i)) =
        fun y : Space => heatKernel ν t y * (c * y i) := by
    funext y
    rw [fderiv_heatKernel_space_apply]
    simp only [c, heatSpatialCoefficient]
    ring
  rw [hrewrite]
  have hG : DifferentiableAt ℝ (fun y : Space => heatKernel ν t y) x :=
    (hasFDerivAt_heatKernel_space ν t x).differentiableAt
  have hcoord : DifferentiableAt ℝ (fun y : Space => c * y i) x := by
    fun_prop
  have hcoord_fderiv :
      fderiv ℝ (fun y : Space => c * y i) x =
        c • (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ) :=
    ((hasFDerivAt_apply i x).const_mul c).fderiv
  change fderiv ℝ
    ((fun y : Space => heatKernel ν t y) * (fun y : Space => c * y i)) x
      (basisVector j) = _
  rw [fderiv_mul hG hcoord]
  rw [hcoord_fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]
  rw [fderiv_heatKernel_space_apply]
  simp only [c, heatSpatialCoefficient]
  ring

/-- The literal mixed third spatial coordinate derivative of the heat
kernel.  The Kronecker factors are represented by coordinates of the
canonical basis vectors, avoiding an auxiliary symbolic derivative carrier. -/
theorem fderiv_fderiv_fderiv_heatKernel_space_apply
    (ν t : ℝ) (i j k : Fin 3) (x : Space) :
    fderiv ℝ
        (fun y : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
            y (basisVector j))
        x (basisVector k) =
      heatKernel ν t x *
        (heatSpatialCoefficient ν t * x k *
            (heatSpatialCoefficient ν t * x j *
              (heatSpatialCoefficient ν t * x i) +
             heatSpatialCoefficient ν t * basisVector j i) +
          heatSpatialCoefficient ν t ^ 2 *
            (basisVector k j * x i + x j * basisVector k i)) := by
  let c : ℝ := heatSpatialCoefficient ν t
  let q : Space → ℝ := fun y =>
    c * y j * (c * y i) + c * basisVector j i
  have hrewrite :
      (fun y : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
            y (basisVector j)) =
        fun y : Space => heatKernel ν t y * q y := by
    funext y
    rw [fderiv_fderiv_heatKernel_space_apply_mixed]
  rw [hrewrite]
  have hG : DifferentiableAt ℝ (fun y : Space => heatKernel ν t y) x :=
    (hasFDerivAt_heatKernel_space ν t x).differentiableAt
  have hq : DifferentiableAt ℝ q x := by
    dsimp only [q]
    fun_prop
  have hq_apply : fderiv ℝ q x (basisVector k) =
      c ^ 2 * (basisVector k j * x i + x j * basisVector k i) := by
    have hji :
        fderiv ℝ (fun y : Space => c * y i) x =
          c • (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ) :=
      ((hasFDerivAt_apply i x).const_mul c).fderiv
    have hjj :
        fderiv ℝ (fun y : Space => c * y j) x =
          c • (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ) :=
      ((hasFDerivAt_apply j x).const_mul c).fderiv
    dsimp only [q]
    rw [fderiv_fun_add]
    · rw [fderiv_fun_mul]
      · rw [hji, hjj]
        simp only [add_apply, fderiv_const_apply, add_zero, smul_apply,
          smul_eq_mul, ContinuousLinearMap.proj_apply]
        ring
      · fun_prop
      · fun_prop
    · fun_prop
    · fun_prop
  change fderiv ℝ ((fun y : Space => heatKernel ν t y) * q) x
      (basisVector k) = _
  rw [fderiv_mul hG hq]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_heatKernel_space_apply]
  rw [hq_apply]
  simp only [q, c, heatSpatialCoefficient]
  ring

/-- Three successive one-coordinate Gaussian moment estimates absorb a cubic
monomial into the heat kernel at eight times the original heat time. -/
private theorem exists_abs_three_coordinates_mul_heatKernel_le_eightfold
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Space) (i j k : Fin 3),
      |x i * x j * x k| * heatKernel ν t x ≤
        C * heatKernel ν (8 * t) x := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν ht
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν (by positivity : 0 < 2 * t)
  obtain ⟨C₄, hC₄, h₄⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν (by positivity : 0 < 4 * t)
  refine ⟨C₁ * C₂ * C₄, by positivity, ?_⟩
  intro x i j k
  have hG : 0 ≤ heatKernel ν t x := heatKernel_nonneg hν ht x
  have hG2 : 0 ≤ heatKernel ν (2 * t) x := heatKernel_nonneg hν (by positivity) x
  have hG4 : 0 ≤ heatKernel ν (4 * t) x := heatKernel_nonneg hν (by positivity) x
  calc
    |x i * x j * x k| * heatKernel ν t x =
        |x i| * (|x j| * (|x k| * heatKernel ν t x)) := by
          rw [abs_mul, abs_mul]
          ring
    _ ≤ |x i| * (|x j| * (C₁ * heatKernel ν (2 * t) x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (h₁ x k) (abs_nonneg _)) (abs_nonneg _)
    _ = C₁ * |x i| * (|x j| * heatKernel ν (2 * t) x) := by ring
    _ ≤ C₁ * |x i| * (C₂ * heatKernel ν (4 * t) x) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [show 2 * (2 * t) = 4 * t by ring] using h₂ x j)
        (mul_nonneg hC₁.le (abs_nonneg _))
    _ = C₁ * C₂ * (|x i| * heatKernel ν (4 * t) x) := by ring
    _ ≤ C₁ * C₂ * (C₄ * heatKernel ν (2 * (4 * t)) x) :=
      mul_le_mul_of_nonneg_left (h₄ x i) (mul_nonneg hC₁.le hC₂.le)
    _ = (C₁ * C₂ * C₄) * heatKernel ν (8 * t) x := by ring

/-- **Mixed third-derivative Gaussian envelope.**  Every coordinate third
derivative is bounded by a cubic-moment contribution at heat time `8t` and
three linear-moment contributions at heat time `2t`.  The constants are
uniform in the three coordinate directions. -/
theorem exists_abs_third_heatKernel_le_gaussians
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (x : Space) (i j k : Fin 3),
      |fderiv ℝ
          (fun y : Space =>
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
              y (basisVector j))
          x (basisVector k)| ≤
        A * heatKernel ν (8 * t) x + B * heatKernel ν (2 * t) x := by
  obtain ⟨C₃, hC₃, h₃⟩ :=
    exists_abs_three_coordinates_mul_heatKernel_le_eightfold hν ht
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν ht
  let c : ℝ := heatSpatialCoefficient ν t
  let A : ℝ := |c| ^ 3 * C₃
  let B : ℝ := 3 * |c| ^ 2 * C₁
  have hc : 0 < |c| := by
    apply abs_pos.mpr
    simp only [c, heatSpatialCoefficient]
    exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by positivity))) (by norm_num)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · simp only [A]
    exact mul_pos (pow_pos hc 3) hC₃
  · simp only [B]
    positivity
  intro x i j k
  have hG : 0 ≤ heatKernel ν t x := heatKernel_nonneg hν ht x
  have hbasis : ∀ r s : Fin 3, |basisVector r s| ≤ 1 := by
    intro r s
    simp only [basisVector, Pi.single_apply]
    split <;> simp
  have hcubic :
      heatKernel ν t x * (|c| ^ 3 * |x i * x j * x k|) ≤
        A * heatKernel ν (8 * t) x := by
    calc
      heatKernel ν t x * (|c| ^ 3 * |x i * x j * x k|) =
          |c| ^ 3 * (|x i * x j * x k| * heatKernel ν t x) := by ring
      _ ≤ |c| ^ 3 * (C₃ * heatKernel ν (8 * t) x) :=
        mul_le_mul_of_nonneg_left (h₃ x i j k) (by positivity)
      _ = A * heatKernel ν (8 * t) x := by simp only [A]; ring
  have hlinear : ∀ r : Fin 3,
      heatKernel ν t x * (|c| ^ 2 * |x r|) ≤
        (|c| ^ 2 * C₁) * heatKernel ν (2 * t) x := by
    intro r
    calc
      heatKernel ν t x * (|c| ^ 2 * |x r|) =
          |c| ^ 2 * (|x r| * heatKernel ν t x) := by ring
      _ ≤ |c| ^ 2 * (C₁ * heatKernel ν (2 * t) x) :=
        mul_le_mul_of_nonneg_left (h₁ x r) (sq_nonneg _)
      _ = (|c| ^ 2 * C₁) * heatKernel ν (2 * t) x := by ring
  rw [fderiv_fderiv_fderiv_heatKernel_space_apply]
  rw [abs_mul, abs_of_nonneg hG]
  have hpoly :
      |c * x k * (c * x j * (c * x i) + c * basisVector j i) +
          c ^ 2 * (basisVector k j * x i + x j * basisVector k i)| ≤
        |c| ^ 3 * |x i * x j * x k| +
          |c| ^ 2 * |x k| + |c| ^ 2 * |x i| + |c| ^ 2 * |x j| := by
    calc
      |c * x k * (c * x j * (c * x i) + c * basisVector j i) +
          c ^ 2 * (basisVector k j * x i + x j * basisVector k i)| =
        |c ^ 3 * (x i * x j * x k) +
          c ^ 2 * (basisVector j i * x k) +
          c ^ 2 * (basisVector k j * x i) +
          c ^ 2 * (basisVector k i * x j)| := by congr 1; ring
      _ ≤ |c ^ 3 * (x i * x j * x k)| +
          |c ^ 2 * (basisVector j i * x k)| +
          |c ^ 2 * (basisVector k j * x i)| +
          |c ^ 2 * (basisVector k i * x j)| := by
        have h₁ := abs_add_le
          (c ^ 3 * (x i * x j * x k))
          (c ^ 2 * (basisVector j i * x k))
        have h₂ := abs_add_le
          (c ^ 3 * (x i * x j * x k) + c ^ 2 * (basisVector j i * x k))
          (c ^ 2 * (basisVector k j * x i))
        have h₃ := abs_add_le
          (c ^ 3 * (x i * x j * x k) + c ^ 2 * (basisVector j i * x k) +
            c ^ 2 * (basisVector k j * x i))
          (c ^ 2 * (basisVector k i * x j))
        linarith
      _ ≤ |c| ^ 3 * |x i * x j * x k| +
          |c| ^ 2 * |x k| + |c| ^ 2 * |x i| + |c| ^ 2 * |x j| := by
        simp only [abs_mul, abs_pow]
        have hk := mul_le_mul_of_nonneg_right (hbasis j i) (abs_nonneg (x k))
        have hi := mul_le_mul_of_nonneg_right (hbasis k j) (abs_nonneg (x i))
        have hj := mul_le_mul_of_nonneg_right (hbasis k i) (abs_nonneg (x j))
        have hk' := mul_le_mul_of_nonneg_left hk (sq_nonneg |c|)
        have hi' := mul_le_mul_of_nonneg_left hi (sq_nonneg |c|)
        have hj' := mul_le_mul_of_nonneg_left hj (sq_nonneg |c|)
        linarith
  calc
    heatKernel ν t x *
        |c * x k * (c * x j * (c * x i) + c * basisVector j i) +
          c ^ 2 * (basisVector k j * x i + x j * basisVector k i)| ≤
      heatKernel ν t x *
        (|c| ^ 3 * |x i * x j * x k| +
          |c| ^ 2 * |x k| + |c| ^ 2 * |x i| + |c| ^ 2 * |x j|) :=
      mul_le_mul_of_nonneg_left hpoly hG
    _ = heatKernel ν t x * (|c| ^ 3 * |x i * x j * x k|) +
        heatKernel ν t x * (|c| ^ 2 * |x k|) +
        heatKernel ν t x * (|c| ^ 2 * |x i|) +
        heatKernel ν t x * (|c| ^ 2 * |x j|) := by ring
    _ ≤ A * heatKernel ν (8 * t) x +
        3 * ((|c| ^ 2 * C₁) * heatKernel ν (2 * t) x) := by
      have hk := hlinear k
      have hi := hlinear i
      have hj := hlinear j
      linarith
    _ = A * heatKernel ν (8 * t) x + B * heatKernel ν (2 * t) x := by
      simp only [B]
      ring

/-- **The third heat-kernel derivatives are square integrable.**  This is the
exact Hilbert-space input needed to pair the cutoff-free viscous test with an
arbitrary finite-energy velocity slice. -/
theorem integrable_abs_third_heatKernel_sq
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i j k : Fin 3) :
    Integrable (fun x : Space =>
      |fderiv ℝ
          (fun y : Space =>
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
              y (basisVector j))
          x (basisVector k)| ^ 2) := by
  obtain ⟨A, B, hA, hB, henv⟩ :=
    exists_abs_third_heatKernel_le_gaussians hν ht
  have hG8 : Integrable (fun x : Space => heatKernel ν (8 * t) x ^ 2) := by
    simpa only [Real.rpow_two] using
      (integrable_heatKernel_rpow hν (by positivity : 0 < 8 * t)
        (s := (2 : ℝ)) (by norm_num))
  have hG2 : Integrable (fun x : Space => heatKernel ν (2 * t) x ^ 2) := by
    simpa only [Real.rpow_two] using
      (integrable_heatKernel_rpow hν (by positivity : 0 < 2 * t)
        (s := (2 : ℝ)) (by norm_num))
  have hmajor : Integrable (fun x : Space =>
      2 * A ^ 2 * heatKernel ν (8 * t) x ^ 2 +
        2 * B ^ 2 * heatKernel ν (2 * t) x ^ 2) :=
    (hG8.const_mul (2 * A ^ 2)).add (hG2.const_mul (2 * B ^ 2))
  have hK : ContDiff ℝ ∞ (fun x : Space => heatKernel ν t x) := by
    unfold heatKernel
    fun_prop
  have hD1 : ContDiff ℝ ∞ (fun x : Space =>
      fderiv ℝ (fun w : Space => heatKernel ν t w) x (basisVector i)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply hK (basisVector i)
  have hD2 : ContDiff ℝ ∞ (fun x : Space =>
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
        x (basisVector j)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply hD1 (basisVector j)
  have hD3 : Continuous (fun x : Space =>
      fderiv ℝ
        (fun y : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
            y (basisVector j))
        x (basisVector k)) :=
    (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hD2 (basisVector k)).continuous
  apply hmajor.mono' (hD3.abs.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  let d : ℝ := |fderiv ℝ
      (fun y : Space =>
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
          y (basisVector j))
      x (basisVector k)|
  let a : ℝ := A * heatKernel ν (8 * t) x
  let b : ℝ := B * heatKernel ν (2 * t) x
  have hd0 : 0 ≤ d := abs_nonneg _
  have ha0 : 0 ≤ a := mul_nonneg hA.le
    (heatKernel_nonneg hν (by positivity) x)
  have hb0 : 0 ≤ b := mul_nonneg hB.le
    (heatKernel_nonneg hν (by positivity) x)
  have hd : d ≤ a + b := henv x i j k
  calc
    d ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [sq_nonneg (a + b - d)]
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    _ = 2 * A ^ 2 * heatKernel ν (8 * t) x ^ 2 +
        2 * B ^ 2 * heatKernel ν (2 * t) x ^ 2 := by
      simp only [a, b]
      ring

/-- Differentiating a reflection-translation contributes one minus sign. -/
private theorem fderiv_const_sub_apply {f : Space → ℝ} {x₀ y v : Space}
    (hf : DifferentiableAt ℝ f (x₀ - y)) :
    fderiv ℝ (fun z : Space => f (x₀ - z)) y v =
      -fderiv ℝ f (x₀ - y) v := by
  have hsub : HasFDerivAt (fun z : Space => x₀ - z)
      (-(1 : Space →L[ℝ] Space)) y :=
    (hasFDerivAt_id y).const_sub x₀
  change fderiv ℝ (f ∘ fun z : Space => x₀ - z) y v = _
  rw [(hf.hasFDerivAt.comp y hsub).fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply]
  rw [map_neg]
  rfl

/-- Three derivatives of a translated heat kernel are the negative of the
corresponding third derivative at the reflected point. -/
theorem fderiv_fderiv_fderiv_heatKernel_translate_apply
    (ν t : ℝ) (x₀ : Space) (i j k : Fin 3) (y : Space) :
    fderiv ℝ
        (fun y' : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
                (basisVector i))
            y' (basisVector j))
        y (basisVector k) =
      -fderiv ℝ
        (fun y' : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t w) z (basisVector i))
            y' (basisVector j))
        (x₀ - y) (basisVector k) := by
  let F : Space → ℝ := fun w => heatKernel ν t w
  let D₁ : Space → ℝ := fun z => fderiv ℝ F z (basisVector i)
  let D₂ : Space → ℝ := fun z => fderiv ℝ D₁ z (basisVector j)
  have hF : ContDiff ℝ ∞ F := by
    dsimp only [F]
    unfold heatKernel
    fun_prop
  have hD₁ : ContDiff ℝ ∞ D₁ := by
    exact Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hF (basisVector i)
  have hD₂ : ContDiff ℝ ∞ D₂ := by
    exact Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hD₁ (basisVector j)
  have hfirst :
      (fun z : Space =>
          fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
            (basisVector i)) =
        fun z : Space => -D₁ (x₀ - z) := by
    funext z
    exact fderiv_const_sub_apply
      ((hF.differentiable (by norm_num)).differentiableAt)
  have hsecond :
      (fun z : Space =>
          fderiv ℝ
            (fun z' : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z'
                (basisVector i))
            z (basisVector j)) =
        fun z : Space => D₂ (x₀ - z) := by
    funext z
    rw [hfirst]
    simp only [fderiv_fun_neg, neg_apply]
    rw [fderiv_const_sub_apply
      ((hD₁.differentiable (by norm_num)).differentiableAt)]
    simp only [D₂, neg_neg]
  rw [hsecond]
  exact fderiv_const_sub_apply
    ((hD₂.differentiable (by norm_num)).differentiableAt)

/-- The translated third derivative has square-integrable absolute value.
This is the directly usable form for a Gaussian centered at the observation
point `x₀`. -/
theorem integrable_abs_third_heatKernel_translate_sq
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x₀ : Space)
    (i j k : Fin 3) :
    Integrable (fun y : Space =>
      |fderiv ℝ
          (fun y' : Space =>
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
                  (basisVector i))
              y' (basisVector j))
          y (basisVector k)| ^ 2) := by
  have hbase := integrable_abs_third_heatKernel_sq hν ht i j k
  have hreflected := hbase.comp_sub_left x₀
  apply hreflected.congr
  filter_upwards with y
  rw [fderiv_fderiv_fderiv_heatKernel_translate_apply]
  simp

/-- **Actual finite-energy consumer.**  At every preterminal time of a
`SolvesBefore` trajectory, a translated third heat-kernel derivative is
integrable when paired with any velocity coordinate.  This closes the
cutoff-free Gaussian term in the viscous slot; the remaining cutoff terms
require only the already-established scaled-cutoff derivative rates. -/
theorem SolvesBefore.integrable_thirdHeatKernel_translate_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x₀ : Space)
    (i j k component : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun y' : Space =>
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
                  (basisVector i))
              y' (basisVector j))
          y (basisVector k) * u s y component) := by
  let D : Space → ℝ := fun y =>
    fderiv ℝ
        (fun y' : Space =>
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
                (basisVector i))
            y' (basisVector j))
        y (basisVector k)
  have hDsq : Integrable (fun y : Space => |D y| ^ 2) :=
    integrable_abs_third_heatKernel_translate_sq hν ht x₀ i j k
  have hDC : Continuous D := by
    dsimp only [D]
    have hK : ContDiff ℝ ∞
        (fun w : Space => heatKernel ν t (x₀ - w)) :=
      Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff ν t x₀
    have hD1 :=
      Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        hK (basisVector i)
    have hD2 :=
      Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        hD1 (basisVector j)
    exact (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hD2 (basisVector k)).continuous
  have hDmem : MemLp D 2 := by
    apply (memLp_two_iff_integrable_sq hDC.aestronglyMeasurable).mpr
    simpa only [sq_abs] using hDsq
  have huC : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hujMeas : AEStronglyMeasurable (fun y : Space => u s y component) :=
    ((continuous_apply component).comp huC.continuous).aestronglyMeasurable
  have hujSqNorm : Integrable (fun y : Space => ‖u s y component‖ ^ 2) := by
    apply (hsol.finite_energy s hs0 hsT).mono' (hujMeas.norm.pow 2)
    filter_upwards with y
    have hcoord : ‖u s y component‖ ≤ ‖u s y‖ := norm_le_pi_norm _ _
    have hcoord0 : 0 ≤ ‖u s y component‖ := norm_nonneg _
    have hfield0 : 0 ≤ ‖u s y‖ := norm_nonneg _
    simp only [Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (‖u s y‖ - ‖u s y component‖)]
  have hujSq : Integrable (fun y : Space => (u s y component) ^ 2) := by
    apply hujSqNorm.congr
    filter_upwards with y
    rw [Real.norm_eq_abs, sq_abs]
  have hujMem : MemLp (fun y : Space => u s y component) 2 :=
    (memLp_two_iff_integrable_sq hujMeas).mpr hujSq
  exact hDmem.integrable_mul hujMem

/-- The cutoff-free solenoidal Gaussian is exactly the cross product of the
translated Gaussian gradient with the constant polarization vector. -/
theorem backwardHeatCurlField_eq_gradient_cross
    (κ τ : ℝ) (x₀ a y : Space) :
    backwardHeatCurlField κ τ x₀ a y =
      staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y ⨯₃ a := by
  unfold backwardHeatCurlField backwardHeatPotential
  rw [staticCurl_smul]
  · simp [staticCurl]
  · exact ((Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff
      κ τ x₀).differentiable (by norm_num)).differentiableAt
  · fun_prop

end Navier.Analysis.WholeSpaceHeatThirdDerivative

#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.fderiv_fderiv_heatKernel_space_apply_mixed
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.fderiv_fderiv_fderiv_heatKernel_space_apply
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.exists_abs_third_heatKernel_le_gaussians
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.integrable_abs_third_heatKernel_sq
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.fderiv_fderiv_fderiv_heatKernel_translate_apply
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.integrable_abs_third_heatKernel_translate_sq
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.SolvesBefore.integrable_thirdHeatKernel_translate_mul_velocity
#print axioms Navier.Analysis.WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross
