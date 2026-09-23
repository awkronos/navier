import Navier.Analysis.WienerGradLog
import Navier.Analysis.GalerkinSmoothBandCutoff
import Navier.Analysis.Ladyzhenskaya

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Navier.Analysis.LittlewoodPaleyPartition

open Navier.Analysis.ContinuousLeiLinSpace

/-!
# Normalized smooth Littlewood--Paley partition

This module constructs one overlapping smooth dyadic cutoff used by both the
exact Fourier-block reconstruction and the uniform inverse-Fourier kernel
estimate. It supersedes disjoint-annulus cutoff candidates that cannot form a
smooth exact partition of unity.
-/



/-- The physical-space scaling used by a three-dimensional dyadic block kernel. -/
def scaledKernel (r : ℝ) (K : ES → ℂ) (x : ES) : ℂ :=
  (r ^ 3) • K (r • x)

/-- Exact inverse-Fourier dilation with Mathlib's `exp(2π i⟨ξ,x⟩)`
normalization. No phase or `2π` correction appears: frequency precomposition
by `r⁻¹` becomes physical precomposition by `r`, with the three-dimensional
Jacobian `r³`. -/
theorem fourierInv_comp_inv_smul (r : ℝ) (hr : 0 < r) (m : ES → ℂ) (x : ES) :
    FourierTransform.fourierInv (fun ξ : ES => m (r⁻¹ • ξ)) x =
      scaledKernel r (FourierTransform.fourierInv m) x := by
  rw [Real.fourierInv_eq]
  unfold scaledKernel
  rw [Real.fourierInv_eq]
  let h : ES → ℂ := fun ξ => 𝐞 (inner ℝ (r • ξ) x) • m ξ
  have hrewrite :
      (fun ξ : ES => 𝐞 (inner ℝ ξ x) • m (r⁻¹ • ξ)) =
        fun ξ : ES => h (r⁻¹ • ξ) := by
    funext ξ
    simp [h, smul_smul, hr.ne']
  rw [hrewrite,
    MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume h hr.le]
  have hdim : Module.finrank ℝ ES = 3 := finrank_euclideanSpace
  rw [hdim]
  congr 1
  congr 1 with ξ
  simp only [h]
  congr 2
  simp [real_inner_smul_left, real_inner_smul_right]

/-- Normalization control: the scaling theorem is literally the identity at
unit scale (the `j = 0` dyadic case). -/
theorem fourierInv_comp_inv_smul_one (m : ES → ℂ) (x : ES) :
    FourierTransform.fourierInv (fun ξ : ES => m ((1 : ℝ)⁻¹ • ξ)) x =
      scaledKernel 1 (FourierTransform.fourierInv m) x :=
  fourierInv_comp_inv_smul 1 zero_lt_one m x

/-- The Riesz quotient is homogeneous of degree zero under the positive
dyadic frequency rescaling. The zero case is explicit, so no cancellation is
performed across `0 / 0`. -/
theorem rieszRatio_inv_smul (j : ℤ) (i k : Fin 3) (x : ES) :
    ((((2 : ℝ) ^ j)⁻¹ • x) k * (((2 : ℝ) ^ j)⁻¹ • x) i /
        ‖((2 : ℝ) ^ j)⁻¹ • x‖ ^ 2) =
      x k * x i / ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hr : 0 < ((2 : ℝ) ^ j)⁻¹ := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    change ((((2 : ℝ) ^ j)⁻¹ * x k) * (((2 : ℝ) ^ j)⁻¹ * x i) /
      (((2 : ℝ) ^ j)⁻¹ * ‖x‖) ^ 2) = x k * x i / ‖x‖ ^ 2
    field_simp [hr.ne', norm_ne_zero_iff.mpr hx]

/-- The scale-normalized dilation of an arbitrary base kernel has exactly the
same `L¹` mass. This is the scaling half of the desired LP2 estimate: once the
unit annular multiplier has an integrable inverse transform `K`, every dyadic
kernel is covered with the same constant `∫ ‖K‖`. -/
theorem integral_norm_scaledKernel (r : ℝ) (hr : 0 < r) (K : ES → ℂ) :
    ∫ x, ‖scaledKernel r K x‖ ∂volume = ∫ x, ‖K x‖ ∂volume := by
  have hpoint : ∀ x : ES, ‖scaledKernel r K x‖ = r ^ 3 * ‖K (r • x)‖ := by
    intro x
    rw [scaledKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr 3)]
  simp only [hpoint, integral_const_mul,
    MeasureTheory.Measure.integral_comp_smul volume (fun x : ES => ‖K x‖) r]
  have hdim : Module.finrank ℝ ES = 3 := finrank_euclideanSpace
  rw [hdim]
  have hi : 0 < (r ^ 3)⁻¹ := by positivity
  rw [abs_of_pos hi]
  simp only [smul_eq_mul]
  field_simp

/-- Integrability transports through the same nonzero dilation. This prevents
the integral identity above from hiding Mathlib's zero-on-nonintegrable
convention when it is used in LP2. -/
theorem integrable_norm_scaledKernel_iff (r : ℝ) (hr : 0 < r) (K : ES → ℂ) :
    Integrable (fun x => ‖scaledKernel r K x‖) volume ↔
      Integrable (fun x => ‖K x‖) volume := by
  have hpoint : (fun x : ES => ‖scaledKernel r K x‖) =
      fun x : ES => r ^ 3 * ‖K (r • x)‖ := by
    funext x
    rw [scaledKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr 3)]
  rw [hpoint]
  constructor
  · intro h
    have hc : r ^ 3 ≠ 0 := (pow_pos hr 3).ne'
    have hs : Integrable (fun x : ES => ‖K (r • x)‖) volume :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc)
        (fun x : ES => ‖K (r • x)‖)).mp h
    exact (MeasureTheory.integrable_comp_smul_iff volume
      (fun x : ES => ‖K x‖) hr.ne').mp hs
  · intro h
    have hs : Integrable (fun x : ES => ‖K (r • x)‖) volume :=
      (MeasureTheory.integrable_comp_smul_iff volume
        (fun x : ES => ‖K x‖) hr.ne').mpr h
    exact hs.const_mul _

/-! The preceding two lemmas discharge LP2's scaling step. The remaining
analytic construction should produce the exact unit-scale multiplier as a
Schwartz map. Mathlib's Fourier automorphism then supplies the required base
kernel integrability directly. -/

/-- The inverse Fourier transform of a Schwartz multiplier is an integrable
kernel, including integrability of its pointwise norm. -/
theorem fourierInv_integrable_norm (m : SchwartzMap ES ℂ) :
    Integrable (fun x : ES =>
      ‖(FourierTransform.fourierInv m : SchwartzMap ES ℂ) x‖) volume :=
  (FourierTransform.fourierInv m : SchwartzMap ES ℂ).integrable.norm

/-- A Schwartz unit multiplier yields a uniform `L¹` estimate for every
positive physical-space scale. For dyadic LP blocks instantiate
`r = 2 ^ j`; no integer-scale arithmetic is needed in the analytic leaf. -/
theorem exists_uniform_L1_of_schwartz_multiplier (m : SchwartzMap ES ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      Integrable (fun x : ES => ‖scaledKernel r
        (FourierTransform.fourierInv m : SchwartzMap ES ℂ) x‖) volume ∧
      (∫ x : ES, ‖scaledKernel r
        (FourierTransform.fourierInv m : SchwartzMap ES ℂ) x‖ ∂volume) ≤ C := by
  refine ⟨∫ x : ES,
    ‖(FourierTransform.fourierInv m : SchwartzMap ES ℂ) x‖ ∂volume,
    integral_nonneg fun _ => norm_nonneg _, ?_⟩
  intro r hr
  constructor
  · exact (integrable_norm_scaledKernel_iff r hr _).mpr
      (fourierInv_integrable_norm m)
  · rw [integral_norm_scaledKernel r hr]

/-! ## One smooth cutoff for both LP1 and LP2

Unlike the earlier cutoff supported in the disjoint open annulus `(1,2)`, the
following standard telescoping cutoff uses an overlapping annulus.  This is
necessary for a smooth exact dyadic partition.
-/

/-- A fixed smooth low-pass plateau, equal to one on the unit ball and zero
outside the ball of radius two. -/
noncomputable def partitionLowPassBump : ContDiffBump (0 : ES) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def partitionLowPass (x : ES) : ℝ := partitionLowPassBump x

theorem partitionLowPass_contDiff :
    ContDiff ℝ (↑(⊤ : ℕ∞)) partitionLowPass :=
  partitionLowPassBump.contDiff

theorem partitionLowPass_eq_one {x : ES} (hx : ‖x‖ ≤ 1) :
    partitionLowPass x = 1 := by
  apply partitionLowPassBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right]

theorem partitionLowPass_eq_zero {x : ES} (hx : 2 ≤ ‖x‖) :
    partitionLowPass x = 0 := by
  apply partitionLowPassBump.zero_of_le_dist
  simpa [dist_zero_right]

/-- The overlapping unit annular cutoff `φ(x) - φ(2x)`. -/
def partitionUnitCutoff (x : ES) : ℝ :=
  partitionLowPass x - partitionLowPass ((2 : ℝ) • x)

theorem partitionUnitCutoff_contDiff :
    ContDiff ℝ (↑(⊤ : ℕ∞)) partitionUnitCutoff :=
  partitionLowPass_contDiff.sub (partitionLowPass_contDiff.comp (by
    exact (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun _ : ES => (2 : ℝ))).smul contDiff_id))

theorem partitionUnitCutoff_eq_zero_of_norm_le_half {x : ES}
    (hx : ‖x‖ ≤ (1 / 2 : ℝ)) : partitionUnitCutoff x = 0 := by
  have hx1 : ‖x‖ ≤ 1 := hx.trans (by norm_num)
  have hx2 : ‖(2 : ℝ) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  simp [partitionUnitCutoff, partitionLowPass_eq_one hx1,
    partitionLowPass_eq_one hx2]

theorem partitionUnitCutoff_eq_zero_of_two_le_norm {x : ES}
    (hx : 2 ≤ ‖x‖) : partitionUnitCutoff x = 0 := by
  have hx2 : 2 ≤ ‖(2 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  simp [partitionUnitCutoff, partitionLowPass_eq_zero hx,
    partitionLowPass_eq_zero hx2]

theorem partitionUnitCutoff_hasCompactSupport :
    HasCompactSupport partitionUnitCutoff := by
  apply (isCompact_closedBall (0 : ES) 2).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (partitionUnitCutoff_eq_zero_of_two_le_norm (le_of_not_ge h))

/-- The dyadic translate of the single unit cutoff. -/
def partitionDyadicCutoff (q : ℤ) (x : ES) : ℝ :=
  partitionUnitCutoff (((2 : ℝ) ^ q)⁻¹ • x)

theorem partitionDyadicCutoff_continuous (q : ℤ) :
    Continuous (partitionDyadicCutoff q) := by
  unfold partitionDyadicCutoff
  have hs : Continuous (fun x : ES => ((2 : ℝ) ^ q)⁻¹ • x) :=
    Continuous.const_smul continuous_id (((2 : ℝ) ^ q)⁻¹)
  exact partitionUnitCutoff_contDiff.continuous.comp hs

theorem partitionDyadicCutoff_telescope (q : ℤ) (x : ES) :
    partitionDyadicCutoff q x =
      partitionLowPass (((2 : ℝ) ^ q)⁻¹ • x) -
      partitionLowPass (((2 : ℝ) ^ (q - 1))⁻¹ • x) := by
  unfold partitionDyadicCutoff partitionUnitCutoff
  congr 2
  rw [smul_smul]
  congr 1
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp

private theorem norm_inv_zpow_smul (q : ℤ) (x : ES) :
    ‖((2 : ℝ) ^ q)⁻¹ • x‖ = ((2 : ℝ) ^ q)⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ q)⁻¹)]

private theorem partitionDyadicCutoff_eq_zero_of_lt_log {x : ES} (hx : x ≠ 0)
    {q : ℤ} (hq : q < Int.log 2 ‖x‖) : partitionDyadicCutoff q x = 0 := by
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hqL : q + 1 ≤ Int.log 2 ‖x‖ := by omega
  have hp : (2 : ℝ) ^ (q + 1) ≤ ‖x‖ :=
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hqL).trans
      (Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) ht)
  have hs : 2 ≤ ‖((2 : ℝ) ^ q)⁻¹ • x‖ := by
    rw [norm_inv_zpow_smul]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ q)).mpr
    calc
      2 * (2 : ℝ) ^ q = (2 : ℝ) ^ q * 2 := by ring
      _ = (2 : ℝ) ^ (q + 1) :=
        (zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0) q).symm
      _ ≤ ‖x‖ := hp
  exact partitionUnitCutoff_eq_zero_of_two_le_norm hs

private theorem partitionDyadicCutoff_eq_zero_of_log_add_one_lt {x : ES} (hx : x ≠ 0)
    {q : ℤ} (hq : Int.log 2 ‖x‖ + 1 < q) : partitionDyadicCutoff q x = 0 := by
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have htop := Int.lt_zpow_succ_log_self (R := ℝ)
    (by norm_num : 1 < (2 : ℕ)) ‖x‖
  have hp : 2 * ‖x‖ ≤ (2 : ℝ) ^ q := by
    have hz : (2 : ℝ) ^ (Int.log 2 ‖x‖ + 2) ≤ (2 : ℝ) ^ q :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc
      2 * ‖x‖ ≤ 2 * (2 : ℝ) ^ (Int.log 2 ‖x‖ + 1) :=
        mul_le_mul_of_nonneg_left htop.le (by norm_num)
      _ = (2 : ℝ) ^ (Int.log 2 ‖x‖ + 1) * 2 := by ring
      _ = (2 : ℝ) ^ ((Int.log 2 ‖x‖ + 1) + 1) :=
        (zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0) _).symm
      _ = (2 : ℝ) ^ (Int.log 2 ‖x‖ + 2) := by congr 1; omega
      _ ≤ (2 : ℝ) ^ q := hz
  have hs : ‖((2 : ℝ) ^ q)⁻¹ • x‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_inv_zpow_smul]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ q)).mpr
    nlinarith
  exact partitionUnitCutoff_eq_zero_of_norm_le_half hs

/-- Exact smooth dyadic resolution of unity away from the origin. -/
theorem tsum_partitionDyadicCutoff (x : ES) (hx : x ≠ 0) :
    (∑' q : ℤ, partitionDyadicCutoff q x) = 1 := by
  let L := Int.log 2 ‖x‖
  have hz : ∀ q ∉ Finset.Icc L (L + 1), partitionDyadicCutoff q x = 0 := by
    intro q hq
    rw [Finset.mem_Icc, not_and_or] at hq
    rcases hq with hq | hq
    · exact partitionDyadicCutoff_eq_zero_of_lt_log hx (by simpa [L] using hq)
    · exact partitionDyadicCutoff_eq_zero_of_log_add_one_lt hx (by simpa [L] using hq)
  rw [tsum_eq_sum hz]
  have hIcc : Finset.Icc L (L + 1) = {L, L + 1} := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hIcc]
  rw [Finset.sum_insert (by simpa using (show L ≠ L + 1 by omega)),
    Finset.sum_singleton]
  rw [partitionDyadicCutoff_telescope, partitionDyadicCutoff_telescope]
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlo := Int.zpow_log_le_self (R := ℝ)
    (by norm_num : 1 < (2 : ℕ)) ht
  have hhi := Int.lt_zpow_succ_log_self (R := ℝ)
    (by norm_num : 1 < (2 : ℕ)) ‖x‖
  have hone : partitionLowPass (((2 : ℝ) ^ (L + 1))⁻¹ • x) = 1 := by
    apply partitionLowPass_eq_one
    rw [norm_inv_zpow_smul]
    rw [inv_mul_eq_div]
    exact (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (L + 1))).mpr hhi.le
  have hzero : partitionLowPass (((2 : ℝ) ^ (L - 1))⁻¹ • x) = 0 := by
    apply partitionLowPass_eq_zero
    rw [norm_inv_zpow_smul]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (L - 1))).mpr
    calc
      2 * (2 : ℝ) ^ (L - 1) = (2 : ℝ) ^ L := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      _ ≤ ‖x‖ := by simpa [L] using hlo
  rw [hone, hzero]
  ring

theorem hasSum_partitionDyadicCutoff (x : ES) (hx : x ≠ 0) :
    HasSum (fun q : ℤ => partitionDyadicCutoff q x) 1 := by
  let L := Int.log 2 ‖x‖
  have hfinite : Function.HasFiniteSupport
      (fun q : ℤ => partitionDyadicCutoff q x) := by
    apply (Finset.finite_toSet (Finset.Icc L (L + 1))).subset
    intro q hq
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · by_contra h
      exact hq (partitionDyadicCutoff_eq_zero_of_lt_log hx (by simpa [L] using h))
    · by_contra h
      exact hq (partitionDyadicCutoff_eq_zero_of_log_add_one_lt hx (by simpa [L] using h))
  have hsumm : Summable (fun q : ℤ => partitionDyadicCutoff q x) :=
    summable_of_hasFiniteSupport hfinite
  have hs := hsumm.hasSum
  rw [tsum_partitionDyadicCutoff x hx] at hs
  exact hs

theorem abs_partitionUnitCutoff_le_one (x : ES) :
    |partitionUnitCutoff x| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    dsimp [partitionUnitCutoff, partitionLowPass] <;>
    linarith [partitionLowPassBump.nonneg' x,
      partitionLowPassBump.le_one (x := x),
      partitionLowPassBump.nonneg' ((2 : ℝ) • x),
      partitionLowPassBump.le_one (x := (2 : ℝ) • x)]

theorem abs_partitionDyadicCutoff_le_one (q : ℤ) (x : ES) :
    |partitionDyadicCutoff q x| ≤ 1 :=
  abs_partitionUnitCutoff_le_one _

theorem tsum_abs_partitionDyadicCutoff_le_two (x : ES) :
    (∑' q : ℤ, |partitionDyadicCutoff q x|) ≤ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [partitionDyadicCutoff, partitionUnitCutoff, partitionLowPass_eq_one]
  · let L := Int.log 2 ‖x‖
    have hz : ∀ q ∉ Finset.Icc L (L + 1),
        |partitionDyadicCutoff q x| = 0 := by
      intro q hq
      rw [Finset.mem_Icc, not_and_or] at hq
      rcases hq with hq | hq
      · rw [partitionDyadicCutoff_eq_zero_of_lt_log hx (by simpa [L] using hq), abs_zero]
      · rw [partitionDyadicCutoff_eq_zero_of_log_add_one_lt hx
          (by simpa [L] using hq), abs_zero]
    rw [tsum_eq_sum hz]
    have hIcc : Finset.Icc L (L + 1) = {L, L + 1} := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hIcc, Finset.sum_insert (by simp), Finset.sum_singleton]
    linarith [abs_partitionDyadicCutoff_le_one L x,
      abs_partitionDyadicCutoff_le_one (L + 1) x]

/-- LP1 frequency-side reconstruction for the actual moment profile. -/
theorem hasSum_partitionedMoment {v : Navier.VelocityField}
    {a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace}
    (_hr : Navier.Analysis.WienerRestartLeaf.Rep v a)
    (ξ : ES) (hξ : ξ ≠ 0) (i k : Fin 3) :
    HasSum (fun q : ℤ => (partitionDyadicCutoff q ξ : ℂ) *
      (((ξ k : ℝ) : ℂ) * a ξ i)) (((ξ k : ℝ) : ℂ) * a ξ i) := by
  simpa only [one_smul, Complex.real_smul, Complex.ofReal_ofNat] using
    (hasSum_partitionDyadicCutoff ξ hξ).smul_const
      (((ξ k : ℝ) : ℂ) * a ξ i : ℂ)

/-- The exact Riesz symbol built from the normalized partition cutoff. -/
def partitionUnitRieszMultiplierReal (i k : Fin 3) (x : ES) : ℝ :=
  (x k * x i / ‖x‖ ^ 2) * partitionUnitCutoff x

theorem partitionUnitRieszMultiplierReal_contDiff (i k : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (partitionUnitRieszMultiplierReal i k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hconst : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : ES => (0 : ℝ)) 0 :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ES) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hnorm : ‖y‖ ≤ (1 / 2 : ℝ) := by
      exact (by simpa [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < 1 / 2).le
    simp [partitionUnitRieszMultiplierReal,
      partitionUnitCutoff_eq_zero_of_norm_le_half hnorm]
  · have hi : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ES => y i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
    have hk : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ES => y k) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt
    have hden : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    exact ((hk.mul hi).div (contDiffAt_id.norm_sq ℝ) hden).mul
      partitionUnitCutoff_contDiff.contDiffAt

theorem partitionUnitRieszMultiplierReal_hasCompactSupport (i k : Fin 3) :
    HasCompactSupport (partitionUnitRieszMultiplierReal i k) :=
  HasCompactSupport.mul_left
    (f := fun x : ES => x k * x i / ‖x‖ ^ 2)
    partitionUnitCutoff_hasCompactSupport

noncomputable def partitionUnitRieszMultiplier (i k : Fin 3) : SchwartzMap ES ℂ :=
  (partitionUnitRieszMultiplierReal_hasCompactSupport i k).comp_left Complex.ofReal_zero
    |>.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp
        (partitionUnitRieszMultiplierReal_contDiff i k))

@[simp]
theorem partitionUnitRieszMultiplier_apply (i k : Fin 3) (x : ES) :
    partitionUnitRieszMultiplier i k x =
      ((x k * x i / ‖x‖ ^ 2) * partitionUnitCutoff x : ℝ) := rfl

def partitionDyadicRieszMultiplier (q : ℤ) (i k : Fin 3) (x : ES) : ℂ :=
  partitionUnitRieszMultiplier i k (((2 : ℝ) ^ q)⁻¹ • x)

def partitionAnnularRieszSymbol (q : ℤ) (i k : Fin 3) (x : ES) : ℂ :=
  ((x k * x i / ‖x‖ ^ 2) * partitionDyadicCutoff q x : ℝ)

theorem partitionAnnularRieszSymbol_eq_multiplier
    (q : ℤ) (i k : Fin 3) (x : ES) :
    partitionAnnularRieszSymbol q i k x =
      partitionDyadicRieszMultiplier q i k x := by
  unfold partitionAnnularRieszSymbol partitionDyadicCutoff
    partitionDyadicRieszMultiplier
  rw [partitionUnitRieszMultiplier_apply, rieszRatio_inv_smul]

def partitionBlockKernel (q : ℤ) (i k : Fin 3) (x : ES) : ℂ :=
  FourierTransform.fourierInv (partitionAnnularRieszSymbol q i k) x

theorem partitionBlockKernel_eq_scaledKernel (q : ℤ) (i k : Fin 3) (x : ES) :
    partitionBlockKernel q i k x = scaledKernel ((2 : ℝ) ^ q)
      (FourierTransform.fourierInv (partitionUnitRieszMultiplier i k) :
        SchwartzMap ES ℂ) x := by
  have heq : partitionAnnularRieszSymbol q i k =
      partitionDyadicRieszMultiplier q i k := by
    funext ξ
    exact partitionAnnularRieszSymbol_eq_multiplier q i k ξ
  rw [partitionBlockKernel, heq]
  unfold partitionDyadicRieszMultiplier
  rw [SchwartzMap.fourierInv_coe]
  exact fourierInv_comp_inv_smul ((2 : ℝ) ^ q) (by positivity)
    (partitionUnitRieszMultiplier i k) x

/-- The same normalized cutoff used by LP1 has the strict uniform LP2 kernel
bound. -/
theorem partitionBlockKernel_L1_uniform (i k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℤ,
      Integrable (fun x : ES => ‖partitionBlockKernel q i k x‖) volume ∧
      (∫ x : ES, ‖partitionBlockKernel q i k x‖ ∂volume) ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_L1_of_schwartz_multiplier (partitionUnitRieszMultiplier i k)
  refine ⟨C, hC0, ?_⟩
  intro q
  simpa only [partitionBlockKernel_eq_scaledKernel] using
    hC ((2 : ℝ) ^ q) (by positivity)

/-- The physical inverse-Fourier moment block using the normalized smooth
partition. -/
def partitionMomentBlock
    (a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace)
    (i k : Fin 3) (q : ℤ) (x : ES) : ℂ :=
  ∫ ξ : ES, 𝐞 (inner ℝ ξ x) •
    ((partitionDyadicCutoff q ξ : ℂ) * (((ξ k : ℝ) : ℂ) * a ξ i))

/-- Actual LP1 smooth block reconstruction on `Rep`.  Absolute summability is
dominated by twice the integrable first moment because at every nonzero
frequency at most two cutoff scales contribute. -/
theorem hasSum_partitionMomentBlock {v : Navier.VelocityField}
    {a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace}
    (hr : Navier.Analysis.WienerRestartLeaf.Rep v a)
    (x : ES) (i k : Fin 3) :
    HasSum (fun q : ℤ => partitionMomentBlock a i k q x)
      (𝓕⁻ (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) x) := by
  have hmoment : Integrable (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) := by
    have hmeas : AEStronglyMeasurable
        (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) volume :=
      ((Complex.measurable_ofReal.comp
        ((PiLp.continuous_apply 2 _ k).comp continuous_id).measurable)
        |>.aestronglyMeasurable).mul
        (((measurable_pi_apply i).comp hr.datum.meas).aestronglyMeasurable)
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    have hle : (fun ξ : ES => ‖((ξ k : ℝ) : ℂ) * a ξ i‖ₑ) ≤ᵐ[volume]
        fun ξ : ES => ENNReal.ofReal ‖ξ‖ * ‖a ξ i‖ₑ := by
      filter_upwards [] with ξ
      rw [enorm_mul]
      exact mul_le_mul' (by
        simpa only [ofReal_norm] using
          (Navier.Analysis.WienerPointwiseODE.enorm_coord_le_norm ξ k)) le_rfl
    exact (lintegral_mono_ae hle).trans_lt (by
      simpa only [pow_one] using (hr.datum.mom_coord 1 i).lt_top)
  let F : ℤ → ES → ℂ := fun q ξ => 𝐞 (inner ℝ ξ x) •
    ((partitionDyadicCutoff q ξ : ℂ) * (((ξ k : ℝ) : ℂ) * a ξ i))
  have hFmeas : ∀ q : ℤ, Measurable (F q) := by
    intro q
    have hcut : Measurable (fun ξ : ES => (partitionDyadicCutoff q ξ : ℂ)) :=
      Complex.measurable_ofReal.comp
        (partitionDyadicCutoff_continuous q).measurable
    have hmom : Measurable (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) :=
      (Complex.measurable_ofReal.comp
        ((PiLp.continuous_apply 2 _ k).comp continuous_id).measurable).mul
          ((measurable_pi_apply i).comp hr.datum.meas)
    have hphase : Measurable (fun ξ : ES => (𝐞 (inner ℝ ξ x) : ℂ)) := by
      simp_rw [Real.fourierChar_apply]
      fun_prop
    rw [show F q = fun ξ : ES => (𝐞 (inner ℝ ξ x) : ℂ) *
      ((partitionDyadicCutoff q ξ : ℂ) * (((ξ k : ℝ) : ℂ) * a ξ i)) by
        funext ξ
        rfl]
    exact hphase.mul (hcut.mul hmom)
  have hlimPoint (ξ : ES) : HasSum (fun q : ℤ => F q ξ)
      (𝐞 (inner ℝ ξ x) • (((ξ k : ℝ) : ℂ) * a ξ i)) := by
    by_cases hξ : ξ = 0
    · subst ξ
      simp [F, partitionDyadicCutoff, partitionUnitCutoff,
        partitionLowPass_eq_one]
    · simpa only [F] using
        (hasSum_partitionedMoment hr ξ hξ i k).const_smul
          (𝐞 (inner ℝ ξ x))
  have hlim : ∀ᵐ ξ : ES, HasSum (fun q : ℤ => F q ξ)
      (𝐞 (inner ℝ ξ x) • (((ξ k : ℝ) : ℂ) * a ξ i)) :=
    Eventually.of_forall hlimPoint
  have hboundSummable : ∀ᵐ ξ : ES, Summable (fun q : ℤ => ‖F q ξ‖) := by
    filter_upwards [] with ξ
    exact (hlimPoint ξ).summable.norm
  have hpoint (ξ : ES) : (∑' q : ℤ, ‖F q ξ‖) ≤
      2 * ‖((ξ k : ℝ) : ℂ) * a ξ i‖ := by
    have heq : (fun q : ℤ => ‖F q ξ‖) = fun q =>
        |partitionDyadicCutoff q ξ| * ‖((ξ k : ℝ) : ℂ) * a ξ i‖ := by
      funext q
      simp only [F, Circle.norm_smul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
    rw [heq, tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (tsum_abs_partitionDyadicCutoff_le_two ξ)
      (norm_nonneg _)
  have hboundInt : Integrable (fun ξ : ES => ∑' q : ℤ, ‖F q ξ‖) := by
    refine (hmoment.norm.const_mul 2).mono'
      ((Measurable.tsum fun q => (hFmeas q).norm).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    calc
      ‖∑' q : ℤ, ‖F q ξ‖‖ = ∑' q : ℤ, ‖F q ξ‖ :=
        Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)
      _ ≤ 2 * ‖((ξ k : ℝ) : ℂ) * a ξ i‖ := hpoint ξ
  have hs := MeasureTheory.hasSum_integral_of_dominated_convergence
    (bound := fun q ξ => ‖F q ξ‖)
    (fun q => (hFmeas q).aestronglyMeasurable)
    (fun q => Eventually.of_forall fun ξ => le_rfl)
    hboundSummable hboundInt hlim
  simpa only [partitionMomentBlock, F, Real.fourierInv_eq] using hs

def partitionGradBlock
    (a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace)
    (i k : Fin 3) (q : ℤ) (x : ES) : ℝ :=
  -(1 / (2 * Real.pi)) *
    (((2 * Real.pi : ℂ) * Complex.I * partitionMomentBlock a i k q x).re)

/-- The exact smooth LP1 series for the physical coordinate derivative.  The
input equality is precisely the independently proved LP0 derivative bridge. -/
theorem hasSum_partitionGradBlock {v : Navier.VelocityField}
    {a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace}
    (hr : Navier.Analysis.WienerRestartLeaf.Rep v a)
    (x : Navier.Space) (i k : Fin 3)
    (hderiv : fderiv ℝ v x (Navier.basisVector k) i =
      -(1 / (2 * Real.pi)) * (((2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i)
          (Navier.Analysis.ContinuousLeiLinPhysicalVelocity.euclidPoint x)).re)) :
    HasSum (fun q : ℤ => partitionGradBlock a i k q
      (Navier.Analysis.ContinuousLeiLinPhysicalVelocity.euclidPoint x))
      (fderiv ℝ v x (Navier.basisVector k) i) := by
  have hc := (hasSum_partitionMomentBlock hr
    (Navier.Analysis.ContinuousLeiLinPhysicalVelocity.euclidPoint x) i k).mul_left
      ((2 * Real.pi : ℂ) * Complex.I)
  have hre := hc.map Complex.reCLM Complex.reCLM.continuous
  have hs := hre.const_smul (-(1 / (2 * Real.pi)))
  simpa only [partitionGradBlock, Function.comp_apply, Complex.reCLM_apply,
    smul_eq_mul, hderiv] using hs

/-! ## LP5 — the low-frequency `L²` block estimate -/

/-- The scale-one weight which carries one Fourier derivative and the normalized
partition cutoff. -/
def partitionLowWeight (x : ES) : ℝ :=
  |partitionUnitCutoff x| * ‖x‖

theorem partitionLowWeight_continuous : Continuous partitionLowWeight := by
  exact (partitionUnitCutoff_contDiff.continuous.abs).mul continuous_norm

theorem partitionLowWeight_hasCompactSupport :
    HasCompactSupport partitionLowWeight := by
  apply partitionUnitCutoff_hasCompactSupport.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  exact hx (by simp [partitionLowWeight, hzero])

theorem integrable_partitionLowWeight_sq :
    Integrable (fun x : ES => partitionLowWeight x ^ 2) := by
  exact (partitionLowWeight_continuous.pow 2).integrable_of_hasCompactSupport
    (by simpa [pow_two] using
      (partitionLowWeight_hasCompactSupport.mul_right
        (f' := partitionLowWeight)))

/-- The fixed scale-one `L²` multiplier constant for the bottom-band estimate. -/
noncomputable def partitionLowConstant : ℝ :=
  Real.sqrt (∫ x : ES, partitionLowWeight x ^ 2)

theorem partitionLowConstant_nonneg : 0 ≤ partitionLowConstant :=
  Real.sqrt_nonneg _

/-- The dyadic derivative weight is exactly a dilation of the scale-one weight. -/
theorem partitionLowWeight_dyadic (q : ℤ) (x : ES) :
    |partitionDyadicCutoff q x| * ‖x‖ =
      (2 : ℝ) ^ q * partitionLowWeight (((2 : ℝ) ^ q)⁻¹ • x) := by
  have hr : 0 < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  unfold partitionDyadicCutoff partitionLowWeight
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  field_simp

/-- Squared bottom-band weights scale by the dimension-plus-two exponent `5`.
This is the exact three-dimensional Cauchy--Schwarz scaling used by LP5. -/
theorem integral_partitionLowWeight_dyadic_sq (q : ℤ) :
    (∫ x : ES, (|partitionDyadicCutoff q x| * ‖x‖) ^ 2) =
      ((2 : ℝ) ^ q) ^ 5 * ∫ x : ES, partitionLowWeight x ^ 2 := by
  let r : ℝ := (2 : ℝ) ^ q
  have hr : 0 < r := zpow_pos (by norm_num) q
  have hdim : Module.finrank ℝ ES = 3 := finrank_euclideanSpace
  simp_rw [partitionLowWeight_dyadic q]
  rw [show (fun x : ES => (r * partitionLowWeight (r⁻¹ • x)) ^ 2) =
      fun x : ES => r ^ 2 * (partitionLowWeight (r⁻¹ • x)) ^ 2 by
        funext x
        ring]
  rw [integral_const_mul,
    MeasureTheory.Measure.integral_comp_smul volume
      (fun x : ES => partitionLowWeight x ^ 2) r⁻¹,
    hdim]
  simp only [inv_pow, inv_inv, abs_pow, abs_of_pos hr, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
/-- General LP5 block estimate.  Its only analytic input is square
integrability of the full profile; the downstream `Rep` consumer supplies that input
directly through `Rep.integrable_profL2_integrand`. -/
theorem norm_partitionMomentBlock_le_L2
    (a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace)
    (ha : Measurable a)
    (hL2 : Integrable (fun ξ : ES => ∑ m : Fin 3, ‖a ξ m‖ ^ 2))
    (i k : Fin 3) (q : ℤ) (x : ES) :
    ‖partitionMomentBlock a i k q x‖ ≤
      Real.sqrt (((2 : ℝ) ^ q) ^ 5 *
        ∫ ξ : ES, partitionLowWeight ξ ^ 2) *
        Navier.Analysis.WienerGradLog.profL2 a := by
  have hai : AEStronglyMeasurable (fun ξ : ES => ‖a ξ i‖) volume :=
    (((measurable_pi_apply i).comp ha).norm).aestronglyMeasurable
  have hai2 : Integrable (fun ξ : ES => ‖a ξ i‖ ^ 2) := by
    refine hL2.mono' (hai.pow 2) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun m _ => sq_nonneg ‖a ξ m‖) (Finset.mem_univ i)
  have hwcont : Continuous (fun ξ : ES =>
      |partitionDyadicCutoff q ξ| * ‖ξ‖) :=
    (partitionDyadicCutoff_continuous q).abs.mul continuous_norm
  have hwcomp : HasCompactSupport (fun ξ : ES =>
      |partitionDyadicCutoff q ξ| * ‖ξ‖) := by
    have hs : HasCompactSupport (partitionDyadicCutoff q) := by
      unfold partitionDyadicCutoff
      exact partitionUnitCutoff_hasCompactSupport.comp_homeomorph
        (Homeomorph.smulOfNeZero ((2 : ℝ) ^ q)⁻¹
          (inv_ne_zero (zpow_ne_zero q (by norm_num))))
    apply hs.mono
    intro ξ hξ
    simp only [Function.mem_support] at hξ ⊢
    intro hzero
    exact hξ (by simp [hzero])
  have hw2 : Integrable (fun ξ : ES =>
      (|partitionDyadicCutoff q ξ| * ‖ξ‖) ^ 2) :=
    (hwcont.pow 2).integrable_of_hasCompactSupport (by
      simpa [pow_two] using
        (hwcomp.mul_right
          (f' := fun ξ : ES => |partitionDyadicCutoff q ξ| * ‖ξ‖)))
  have hwLp : MemLp (fun ξ : ES =>
      |partitionDyadicCutoff q ξ| * ‖ξ‖) 2 volume :=
    (memLp_two_iff_integrable_sq hwcont.aestronglyMeasurable).mpr hw2
  have haiLp : MemLp (fun ξ : ES => ‖a ξ i‖) 2 volume :=
    (memLp_two_iff_integrable_sq hai).mpr hai2
  have hprod : Integrable (fun ξ : ES =>
      (|partitionDyadicCutoff q ξ| * ‖ξ‖) * ‖a ξ i‖) := by
    change Integrable ((fun ξ : ES => |partitionDyadicCutoff q ξ| * ‖ξ‖) *
      (fun ξ : ES => ‖a ξ i‖))
    exact hwLp.integrable_mul haiLp
  have hcs := Navier.Analysis.Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt
    (μ := volume)
    (f := fun ξ : ES => |partitionDyadicCutoff q ξ| * ‖ξ‖)
    (g := fun ξ : ES => ‖a ξ i‖)
    (fun ξ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
    (fun ξ => norm_nonneg _)
    hwcont.aestronglyMeasurable hai hw2 hai2
  have hcoord : Real.sqrt (∫ ξ : ES, ‖a ξ i‖ ^ 2) ≤
      Navier.Analysis.WienerGradLog.profL2 a := by
    unfold Navier.Analysis.WienerGradLog.profL2
    exact Real.sqrt_le_sqrt (integral_mono_ae hai2 hL2
      (Eventually.of_forall fun ξ =>
        Finset.single_le_sum (fun m _ => sq_nonneg ‖a ξ m‖) (Finset.mem_univ i)))
  have horig : Integrable (fun ξ : ES =>
      ‖𝐞 (inner ℝ ξ x) •
        ((partitionDyadicCutoff q ξ : ℂ) * (((ξ k : ℝ) : ℂ) * a ξ i))‖) := by
    have hnormeq : (fun ξ : ES =>
        ‖𝐞 (inner ℝ ξ x) •
          ((partitionDyadicCutoff q ξ : ℂ) * (((ξ k : ℝ) : ℂ) * a ξ i))‖) =
        fun ξ : ES => |partitionDyadicCutoff q ξ| * |ξ k| * ‖a ξ i‖ := by
      funext ξ
      simp only [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    rw [hnormeq]
    refine hprod.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (((partitionDyadicCutoff_continuous q).measurable.abs.mul
          (((PiLp.continuous_apply 2 _ k).comp continuous_id).measurable.abs)).mul
          (((measurable_pi_apply i).comp ha).norm)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))]
      have hk : |ξ k| ≤ ‖ξ‖ := by
        simpa [Real.norm_eq_abs] using
          (PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) ξ k)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (abs_nonneg (partitionDyadicCutoff q ξ)))
        (norm_nonneg (a ξ i))
  calc
    ‖partitionMomentBlock a i k q x‖
        ≤ ∫ ξ : ES, |partitionDyadicCutoff q ξ| * ‖ξ‖ * ‖a ξ i‖ := by
          rw [partitionMomentBlock]
          refine (norm_integral_le_integral_norm _).trans
            (MeasureTheory.integral_mono_ae horig hprod ?_)
          · filter_upwards [] with ξ
            simp only [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hk : |ξ k| ≤ ‖ξ‖ := by
              simpa [Real.norm_eq_abs] using
                (PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) ξ k)
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hk (abs_nonneg (partitionDyadicCutoff q ξ)))
              (norm_nonneg (a ξ i))
    _ ≤ Real.sqrt (∫ ξ : ES,
          (|partitionDyadicCutoff q ξ| * ‖ξ‖) ^ 2) *
          Real.sqrt (∫ ξ : ES, ‖a ξ i‖ ^ 2) := hcs
    _ ≤ Real.sqrt (∫ ξ : ES,
          (|partitionDyadicCutoff q ξ| * ‖ξ‖) ^ 2) *
          Navier.Analysis.WienerGradLog.profL2 a := by
            exact mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg _)
    _ = _ := by rw [integral_partitionLowWeight_dyadic_sq]

private theorem sqrt_pow_five_le_sq {r A : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.sqrt (r ^ 5 * A) ≤ r ^ 2 * Real.sqrt A := by
  rw [Real.sqrt_mul (pow_nonneg hr0 5)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg A)
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      r ^ 5 = r ^ 4 * r := by ring
      _ ≤ r ^ 4 * 1 := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 4)
      _ = (r ^ 2) ^ 2 := by ring

/-- The actual bottom-shell form consumed by the existing `shellSum_log`
envelope: at scale `q = -j`, the block is bounded by a fixed constant times
`profL2 a` and the geometric factor `4⁻ʲ`. -/
theorem norm_partitionMomentBlock_neg_le_L2
    (a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace)
    (ha : Measurable a)
    (hL2 : Integrable (fun ξ : ES => ∑ m : Fin 3, ‖a ξ m‖ ^ 2))
    (i k : Fin 3) (j : ℕ) (x : ES) :
    ‖partitionMomentBlock a i k (-(j : ℤ)) x‖ ≤
      (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
        ((1 : ℝ) / 4) ^ j := by
  let r : ℝ := (2 : ℝ) ^ (-(j : ℤ))
  have hr0 : 0 ≤ r := (zpow_pos (by norm_num) _).le
  have hr1 : r ≤ 1 := by
    change (2 : ℝ) ^ (-(j : ℤ)) ≤ 1
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hs := norm_partitionMomentBlock_le_L2 a ha hL2 i k (-(j : ℤ)) x
  have hscale : Real.sqrt (r ^ 5 * ∫ ξ : ES, partitionLowWeight ξ ^ 2) ≤
      r ^ 2 * partitionLowConstant := by
    simpa only [partitionLowConstant] using sqrt_pow_five_le_sq hr0 hr1
  calc
    ‖partitionMomentBlock a i k (-(j : ℤ)) x‖
        ≤ Real.sqrt (r ^ 5 * ∫ ξ : ES, partitionLowWeight ξ ^ 2) *
            Navier.Analysis.WienerGradLog.profL2 a := by simpa only [r] using hs
    _ ≤ (r ^ 2 * partitionLowConstant) *
          Navier.Analysis.WienerGradLog.profL2 a :=
      mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg _)
    _ = (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
          ((1 : ℝ) / 4) ^ j := by
      have hr2 : r ^ 2 = ((1 : ℝ) / 4) ^ j := by
        change ((2 : ℝ) ^ (-(j : ℤ))) ^ 2 = ((1 : ℝ) / 4) ^ j
        rw [zpow_neg, zpow_natCast, inv_pow]
        norm_num [div_pow]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
      rw [hr2]
      ring

/-- Scale-zero normalization control for the LP5 estimate. -/
theorem norm_partitionMomentBlock_zero_le_L2
    (a : ES → Navier.Analysis.ContinuousLeiLinSpace.ComplexSpace)
    (ha : Measurable a)
    (hL2 : Integrable (fun ξ : ES => ∑ m : Fin 3, ‖a ξ m‖ ^ 2))
    (i k : Fin 3) (x : ES) :
    ‖partitionMomentBlock a i k 0 x‖ ≤
      partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a := by
  simpa using norm_partitionMomentBlock_neg_le_L2 a ha hL2 i k 0 x



end Navier.Analysis.LittlewoodPaleyPartition

set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyPartition.tsum_partitionDyadicCutoff
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.tsum_partitionDyadicCutoff
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.hasSum_partitionDyadicCutoff
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.partitionUnitRieszMultiplierReal_contDiff
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.partitionAnnularRieszSymbol_eq_multiplier
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.partitionBlockKernel_eq_scaledKernel
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.partitionBlockKernel_L1_uniform
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyPartition.hasSum_partitionMomentBlock
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.hasSum_partitionMomentBlock
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.hasSum_partitionGradBlock
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.integral_partitionLowWeight_dyadic_sq
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyPartition.norm_partitionMomentBlock_le_L2
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.norm_partitionMomentBlock_le_L2
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyPartition.norm_partitionMomentBlock_neg_le_L2
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.norm_partitionMomentBlock_neg_le_L2
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPartition.norm_partitionMomentBlock_zero_le_L2
