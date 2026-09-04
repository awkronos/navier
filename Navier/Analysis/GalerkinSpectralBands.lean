import Navier.Analysis.FourierWeightedPlancherel

/-!
# Fourier-band estimates for the whole-space Galerkin construction

On a frequency annulus with outer radius twice its inner radius, the
Dirichlet energy is equivalent to the squared `L²` norm with ratio four.
This is the analytic estimate needed for uniformly bounded orthogonal
projections within each band. The bandwise divergence-free dense families
and their assembly into the original Galerkin basis remain to be constructed.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace Navier.Analysis.GalerkinSpectralBands

abbrev ES := EuclideanSpace ℝ (Fin 3)

section RealProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The canonical map from Schwartz functions to their actual `L²` classes. -/
def schwartzL2 : 𝓢(ES, H) →L[ℝ] Lp H 2 (volume : Measure ES) :=
  SchwartzMap.toLpCLM ℝ H 2 volume

theorem schwartzL2_norm_sq (f : 𝓢(ES, H)) :
    ‖schwartzL2 f‖ ^ 2 = ∫ x : ES, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp f 2 (volume : Measure ES)] with x hx
  change inner ℝ ((f.toLp 2 volume) x) ((f.toLp 2 volume) x) = ‖f x‖ ^ 2
  rw [hx, real_inner_self_eq_norm_sq]

/-- Finite orthogonal projection, represented by a Schwartz function. -/
def schwartzProjection {ι : Type*} [Fintype ι]
    (w : ι → 𝓢(ES, H)) (f : 𝓢(ES, H)) : 𝓢(ES, H) :=
  ∑ i, (inner ℝ (schwartzL2 (w i)) (schwartzL2 f)) • w i

theorem schwartzProjection_L2_le {ι : Type*} [Fintype ι]
    (w : ι → 𝓢(ES, H)) (hw : Orthonormal ℝ (fun i => schwartzL2 (w i)))
    (f : 𝓢(ES, H)) : ‖schwartzL2 (schwartzProjection w f)‖ ≤ ‖schwartzL2 f‖ := by
  classical
  let c : ι → ℝ := fun i => inner ℝ (schwartzL2 (w i)) (schwartzL2 f)
  have hp : schwartzL2 (schwartzProjection w f) = ∑ i, c i • schwartzL2 (w i) := by
    simp [schwartzProjection, c]
  have heq : inner ℝ (schwartzL2 (schwartzProjection w f)) (schwartzL2 f) =
      ‖schwartzL2 (schwartzProjection w f)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hp]
    rw [hw.inner_sum c c Finset.univ]
    simp only [sum_inner, inner_smul_left, conj_trivial]
    rfl
  have hcs := real_inner_le_norm (schwartzL2 (schwartzProjection w f)) (schwartzL2 f)
  rw [heq] at hcs
  have hg := norm_nonneg (schwartzL2 (schwartzProjection w f))
  have hf := norm_nonneg (schwartzL2 f)
  nlinarith

end RealProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Square integrability of a Hilbert-valued Schwartz function. -/
theorem schwartz_normSq_integrable (f : 𝓢(ES, H)) :
    Integrable (fun x : ES => ‖f x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  have hbound : ∀ x, ‖f x‖ ≤ C := by
    intro x
    simpa using hC x
  refine (f.integrable.norm.const_mul C).mono'
    ((map_continuous f).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (f x))]

/-- Actual Fourier support in an annulus bounds its weighted energy above
and below by the physical `L²` mass. Plancherel supplies the exact comparison.
-/
theorem fourierBand_dirichlet_bounds
    (f : 𝓢(ES, H)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hband : ∀ ξ : ES, (𝓕 f) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) :
    a ^ 2 * (∫ x : ES, ‖f x‖ ^ 2) ≤
        ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 ∧
      (∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) ≤
        b ^ 2 * (∫ x : ES, ‖f x‖ ^ 2) := by
  have hupper : ∀ ξ : ES,
      ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 ≤ b ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
    intro ξ
    by_cases hz : (𝓕 f) ξ = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg ξ) (hband ξ hz).2 2) (sq_nonneg _)
  have hweighted : Integrable (fun ξ : ES => ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
    refine ((schwartz_normSq_integrable (𝓕 f)).const_mul (b ^ 2)).mono'
      (by fun_prop) ?_
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hupper ξ
  have hlower : ∀ ξ : ES,
      a ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
    intro ξ
    by_cases hz : (𝓕 f) ξ = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ ha (hband ξ hz).1 2) (sq_nonneg _)
  constructor
  · have h := integral_mono
      ((schwartz_normSq_integrable (𝓕 f)).const_mul (a ^ 2)) hweighted hlower
    simpa only [integral_const_mul, SchwartzMap.integral_norm_sq_fourier] using h
  · have h := integral_mono hweighted
      ((schwartz_normSq_integrable (𝓕 f)).const_mul (b ^ 2)) hupper
    simpa only [integral_const_mul, SchwartzMap.integral_norm_sq_fourier] using h

/-- An `L²` contraction between functions in one dyadic frequency band costs
at most a factor four in Dirichlet energy. This bound is independent of the
band's scale and the dimension of the retained finite span. -/
theorem dyadicBand_L2_contraction_dirichlet
    (f g : 𝓢(ES, H)) {a : ℝ} (ha : 0 < a)
    (hf : ∀ ξ : ES, (𝓕 f) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hg : ∀ ξ : ES, (𝓕 g) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hL2 : (∫ x : ES, ‖g x‖ ^ 2) ≤ ∫ x : ES, ‖f x‖ ^ 2) :
    (∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 g) ξ‖ ^ 2) ≤
      4 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hfb := (fourierBand_dirichlet_bounds f ha.le (by positivity) hf).1
  have hgb := (fourierBand_dirichlet_bounds g ha.le (by positivity) hg).2
  have hmass := mul_le_mul_of_nonneg_left hL2 (sq_nonneg a)
  nlinarith

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
attribute [local instance 2000] MeasureTheory.L2.innerProductSpace

/-- Finite orthogonal projection preserves the common Fourier band. -/
theorem schwartzProjection_fourierBand {ι : Type*} [Fintype ι]
    (w : ι → 𝓢(ES, H)) (f : 𝓢(ES, H)) {a b : ℝ}
    (hband : ∀ i ξ, (𝓕 (w i)) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) :
    ∀ ξ, (𝓕 (schwartzProjection w f)) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b := by
  classical
  intro ξ hξ
  by_contra hout
  apply hξ
  have hz : ∀ i, (𝓕 (w i)) ξ = 0 := by
    intro i
    by_contra hi
    exact hout (hband i ξ hi)
  change ((SchwartzMap.fourierTransformCLM ℝ) (schwartzProjection w f)) ξ = 0
  simp [schwartzProjection, map_sum, hz]

/-- Actual finite orthogonal projections within one dyadic Fourier band have
Dirichlet energy bounded by four times the input energy, uniformly in the
number of retained vectors and the band's scale. -/
theorem schwartzProjection_dyadicBand_dirichlet {ι : Type*} [Fintype ι]
    (w : ι → 𝓢(ES, H)) (hw : Orthonormal ℝ (fun i => schwartzL2 (w i)))
    (f : 𝓢(ES, H)) {a : ℝ} (ha : 0 < a)
    (hf : ∀ ξ, (𝓕 f) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hband : ∀ i ξ, (𝓕 (w i)) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a) :
    (∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 (schwartzProjection w f)) ξ‖ ^ 2) ≤
      4 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  apply dyadicBand_L2_contraction_dirichlet f _ ha hf
    (schwartzProjection_fourierBand w f hband)
  rw [← schwartzL2_norm_sq, ← schwartzL2_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (schwartzProjection_L2_le w hw f) 2

end Navier.Analysis.GalerkinSpectralBands
