import Navier.Analysis.ContinuousLeiLinPhysicalRegularity
import Navier.Analysis.ContinuousLeiLinDissipation
import Navier.Analysis.CriticalMildHeatSmoothing

/-!
# Smooth physical slices from Fourier moments

The first-moment module gives the scale-sensitive `C¹` bound needed by a
local classical theory.  Here the same inverse-Fourier mechanism transports
all available polynomial moments: moments through `N` yield `C^N`, and all
moments at a positive-time trajectory slice yield spatial `C∞` regularity.

This isolates the exact smoothing premise that a mild-solution construction
must establish before it can feed a classical restart theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Navier.Analysis.ContinuousLeiLinPhysicalSmoothing

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.CriticalMildHeatSmoothing

/-- Arbitrary polynomial frequency gain from a positive Gaussian time.  The
proof splits the heat exponential into `k` equal factors and applies the
existing sharp-order one-frequency estimate to each factor. -/
theorem pow_mul_exp_neg_mul_sq_le {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (k : ℕ) :
    r ^ k * Real.exp (-(a * r * r)) ≤
      (Real.sqrt (a / (k : ℝ)))⁻¹ ^ k := by
  rcases k with _ | k
  · simp only [pow_zero, one_mul]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg ha.le hr) hr)
  · have hkn : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hak : 0 < a / ((k + 1 : ℕ) : ℝ) := div_pos ha hkn
    have hbase := mul_exp_neg_mul_sq_le_inv_sqrt
      (a := a / ((k + 1 : ℕ) : ℝ)) (r := r) hak
    have hexp : Real.exp (-(a * r * r)) =
        Real.exp (-((a / ((k + 1 : ℕ) : ℝ)) * r * r)) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    rw [hexp, ← mul_pow]
    gcongr

/-- Positive heat time turns a single `X⁻¹` Fourier density into every
polynomially weighted integrable density.  The value at frequency zero is
discarded only through the canonical Lebesgue-null singleton. -/
theorem integrable_pow_norm_heatMode_of_Xm1 (f : ES → ℂ)
    (hf : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (n : ℕ) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖heatMode ν t f ξ‖) := by
  let k : ℕ := n + 1
  let a : ℝ := ν * t
  let C : ℝ := (Real.sqrt (a / (k : ℝ)))⁻¹ ^ k
  have ha : 0 < a := mul_pos hν ht
  have hk : 0 < (k : ℝ) := by
    simp only [k, Nat.cast_add, Nat.cast_one]
    positivity
  have hC : 0 ≤ C :=
    pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  have hne : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton (μ := (volume : Measure ES)) (0 : ES))
  have heq : ∀ᵐ ξ : ES ∂volume,
      ‖ξ‖ ^ n * ‖heatMode ν t f ξ‖ =
        (‖ξ‖ ^ k * Real.exp (-(a * ‖ξ‖ * ‖ξ‖))) *
          (‖ξ‖⁻¹ * ‖f ξ‖) := by
    filter_upwards [hne] with ξ hξ
    have hr : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    simp only [heatMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    dsimp [a, k]
    field_simp
    ring
  have hmajor : ∀ᵐ ξ : ES ∂volume,
      ‖‖ξ‖ ^ n * ‖heatMode ν t f ξ‖‖ ≤ C * (‖ξ‖⁻¹ * ‖f ξ‖) := by
    filter_upwards [hne, heq] with ξ hξ heqξ
    rw [heqξ, Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)))]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    exact pow_mul_exp_neg_mul_sq_le ha (norm_nonneg ξ) k
  refine (hf.const_mul C).mono' ?_ hmajor
  have hmult : AEStronglyMeasurable (fun ξ : ES =>
      ‖ξ‖ ^ k * Real.exp (-(a * ‖ξ‖ * ‖ξ‖))) := by
    fun_prop
  exact (hmult.mul hf.aestronglyMeasurable).congr (Filter.EventuallyEq.symm heq)

/-- Quantitative form of positive-time heat smoothing.  Its displayed
constant has the parabolic scale `(νt)^(-(n+1)/2)` relative to `X⁻¹`. -/
theorem integral_pow_norm_heatMode_le_Xm1 (f : ES → ℂ)
    (hf : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (n : ℕ) :
    (∫ ξ : ES, ‖ξ‖ ^ n * ‖heatMode ν t f ξ‖) ≤
      (Real.sqrt (ν * t / ((n + 1 : ℕ) : ℝ)))⁻¹ ^ (n + 1) * normXm1 f := by
  let C : ℝ := (Real.sqrt (ν * t / ((n + 1 : ℕ) : ℝ)))⁻¹ ^ (n + 1)
  have hne : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton (μ := (volume : Measure ES)) (0 : ES))
  have hle : ∀ᵐ ξ : ES ∂volume,
      ‖ξ‖ ^ n * ‖heatMode ν t f ξ‖ ≤ C * (‖ξ‖⁻¹ * ‖f ξ‖) := by
    filter_upwards [hne] with ξ hξ
    have hr : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    simp only [heatMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have heq : ‖ξ‖ ^ n * (Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖) =
        (‖ξ‖ ^ (n + 1) * Real.exp (-((ν * t) * ‖ξ‖ * ‖ξ‖))) *
          (‖ξ‖⁻¹ * ‖f ξ‖) := by
      field_simp
      ring
    rw [heq]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    exact pow_mul_exp_neg_mul_sq_le (mul_pos hν ht) (norm_nonneg ξ) (n + 1)
  have htarget := integrable_pow_norm_heatMode_of_Xm1 f hf ν t hν ht n
  have hmajor : Integrable (fun ξ : ES => C * (‖ξ‖⁻¹ * ‖f ξ‖)) := hf.const_mul C
  calc
    (∫ ξ : ES, ‖ξ‖ ^ n * ‖heatMode ν t f ξ‖) ≤
        ∫ ξ : ES, C * (‖ξ‖⁻¹ * ‖f ξ‖) := integral_mono_ae htarget hmajor hle
    _ = C * normXm1 f := by rw [integral_const_mul]; rfl

/-- Coordinatewise version of positive-time heat smoothing. -/
theorem integrable_pow_norm_heatVec_of_Xm1
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (i : Fin 3) (n : ℕ) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖heatVec ν t a ξ i‖) := by
  exact integrable_pow_norm_heatMode_of_Xm1 (fun ξ => a ξ i) (ha i) ν t hν ht n

/-- Integrable Fourier moments through order `N` produce `C^N` inverse
Fourier regularity. -/
theorem contDiff_fourierInv_of_integrable_moments {N : ℕ∞} (f : ES → ℂ)
    (hmom : ∀ n : ℕ, n ≤ N → Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖f ξ‖)) :
    ContDiff ℝ N (FourierTransform.fourierInv f) := by
  let L : ES →L[ℝ] ES →L[ℝ] ℝ :=
    -(innerSL ℝ : ES →L[ℝ] ES →L[ℝ] ℝ)
  have hL : L.toLinearMap₁₂ = -innerₗ ES := rfl
  simpa only [FourierTransform.fourierInv, hL] using
    (VectorFourier.contDiff_fourierIntegral (L := L) hmom)

/-- All polynomial moments of one Fourier coordinate make its reconstructed
physical coordinate spatially smooth. -/
theorem contDiff_infty_physicalCoord_of_integrable_moments
    (w : ES → ComplexSpace) (i : Fin 3)
    (hmom : ∀ n : ℕ, Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖w ξ i‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoord w i) := by
  apply contDiff_fourierInv_of_integrable_moments (N := ⊤) (fun ξ => w ξ i)
  intro n _
  exact hmom n

/-- A trajectory with all Fourier moments at every positive time reconstructs
to a spatially smooth physical velocity at every positive-time slice. -/
theorem contDiff_infty_physicalCoord_slice_of_integrable_moments
    (w : ℝ → ES → ComplexSpace)
    (hmom : ∀ t : ℝ, 0 < t → ∀ i : Fin 3, ∀ n : ℕ,
      Integrable (fun ξ : ES => ‖ξ‖ ^ n * ‖w t ξ i‖))
    {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoord (w t) i) := by
  exact contDiff_infty_physicalCoord_of_integrable_moments (w t) i (hmom t ht i)

/-- The free Navier--Stokes heat evolution of `X⁻¹` data is spatially `C∞`
at every positive time, in the actual reconstructed physical carrier. -/
theorem contDiff_infty_physicalCoord_heatVec_of_Xm1
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoord (heatVec ν t a) i) := by
  apply contDiff_infty_physicalCoord_of_integrable_moments
  exact fun n => integrable_pow_norm_heatVec_of_Xm1 a ha ν t hν ht i n

end Navier.Analysis.ContinuousLeiLinPhysicalSmoothing

#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_fourierInv_of_integrable_moments
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_of_integrable_moments
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_slice_of_integrable_moments
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.pow_mul_exp_neg_mul_sq_le
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integrable_pow_norm_heatMode_of_Xm1
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integral_pow_norm_heatMode_le_Xm1
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integrable_pow_norm_heatVec_of_Xm1
#check Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_heatVec_of_Xm1

#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_fourierInv_of_integrable_moments
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_of_integrable_moments
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_slice_of_integrable_moments
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.pow_mul_exp_neg_mul_sq_le
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integrable_pow_norm_heatMode_of_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integral_pow_norm_heatMode_le_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.integrable_pow_norm_heatVec_of_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalSmoothing.contDiff_infty_physicalCoord_heatVec_of_Xm1
