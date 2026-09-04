import Navier.Analysis.DivFreeGradientEnstrophy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The transverse Fourier projection

The multiplier is the actual orthogonal projection onto the plane normal to
the real frequency vector. It keeps pairings with divergence-free Fourier
vectors and preserves the curl symbol. Its value at zero is the identity,
the orthogonal projection onto the whole space.
-/

noncomputable section
open scoped BigOperators

namespace Navier.Analysis.FourierTransverseProjection

abbrev ES := EuclideanSpace ℝ (Fin 3)
abbrev CS := EuclideanSpace ℂ (Fin 3)

def frequencyVector (ξ : ES) : CS := WithLp.toLp 2 (fun i => (ξ i : ℂ))

@[simp] theorem frequencyVector_apply (ξ : ES) (i : Fin 3) :
    frequencyVector ξ i = (ξ i : ℂ) := rfl

def transversePlane (ξ : ES) : Submodule ℂ CS :=
  (Submodule.span ℂ {frequencyVector ξ})ᗮ

def transverseProjection (ξ : ES) : CS →L[ℂ] CS :=
  (transversePlane ξ).starProjection

/-- Orthogonal projection removes precisely the longitudinal component. -/
theorem transverseProjection_eq (ξ : ES) (z : CS) :
    transverseProjection ξ z = z -
      (inner ℂ (frequencyVector ξ) z / (‖frequencyVector ξ‖ ^ 2 : ℝ)) •
        frequencyVector ξ := by
  change (Submodule.span ℂ {frequencyVector ξ})ᗮ.starProjection z = _
  rw [Submodule.starProjection_orthogonal]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    Submodule.starProjection_singleton]
  rfl

theorem inner_frequency_transverseProjection (ξ : ES) (z : CS) :
    inner ℂ (frequencyVector ξ) (transverseProjection ξ z) = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((transversePlane ξ).starProjection_apply_mem z)

theorem transverseProjection_norm_le (ξ : ES) (z : CS) :
    ‖transverseProjection ξ z‖ ≤ ‖z‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg z)
      ((transversePlane ξ).starProjection_norm_le))

/-- Pairing a transverse vector with the input sees only its transverse
component. This is the projection identity needed for arbitrary input
velocities in the original `H(curl)` stability statement. -/
theorem inner_transverseProjection_right (ξ : ES) (w z : CS)
    (hw : inner ℂ (frequencyVector ξ) w = 0) :
    inner ℂ w (transverseProjection ξ z) = inner ℂ w z := by
  have hmem : w ∈ transversePlane ξ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw
  have hfix : transverseProjection ξ w = w :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  change inner ℂ w ((transversePlane ξ).starProjection z) = _
  rw [← (transversePlane ξ).inner_starProjection_left_eq_right w z]
  rw [show (transversePlane ξ).starProjection w = w from hfix]

/-- All components of the curl multiplier are unchanged by the transverse
projection, including at frequency zero. -/
theorem transverseProjection_curlSymbol (ξ : ES) (z : CS) (i j : Fin 3) :
    (ξ i : ℂ) * transverseProjection ξ z j -
        (ξ j : ℂ) * transverseProjection ξ z i =
      (ξ i : ℂ) * z j - (ξ j : ℂ) * z i := by
  rw [transverseProjection_eq]
  simp only [PiLp.sub_apply, PiLp.smul_apply, frequencyVector_apply, smul_eq_mul]
  ring

/-- Squared magnitude of the three components of the curl symbol, with the
common Fourier factor `2πi` omitted. -/
def curlSymbolEnergy (ξ : ES) (z : CS) : ℝ :=
  ‖(ξ 1 : ℂ) * z 2 - (ξ 2 : ℂ) * z 1‖ ^ 2 +
    ‖(ξ 2 : ℂ) * z 0 - (ξ 0 : ℂ) * z 2‖ ^ 2 +
    ‖(ξ 0 : ℂ) * z 1 - (ξ 1 : ℂ) * z 0‖ ^ 2

private theorem complex_norm_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem curlSymbolEnergy_lagrange (ξ : ES) (z : CS) :
    curlSymbolEnergy ξ z = ‖ξ‖ ^ 2 * ‖z‖ ^ 2 -
      ‖∑ i : Fin 3, (ξ i : ℂ) * z i‖ ^ 2 := by
  have hξ : ‖ξ‖ ^ 2 = ∑ i : Fin 3, (ξ i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]
  have hz : ‖z‖ ^ 2 = ∑ i : Fin 3, ‖z i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rw [curlSymbolEnergy, hξ, hz]
  simp only [Fin.sum_univ_three, complex_norm_sq, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The transverse part carries exactly the curl energy at every frequency.
Together with `inner_transverseProjection_right`, this permits bounds on
arbitrary input fields without assuming that the input is divergence-free. -/
theorem transverseProjection_weighted_norm_sq (ξ : ES) (z : CS) :
    ‖ξ‖ ^ 2 * ‖transverseProjection ξ z‖ ^ 2 = curlSymbolEnergy ξ z := by
  have hdot : ∑ i : Fin 3, (ξ i : ℂ) * transverseProjection ξ z i = 0 := by
    have h := inner_frequency_transverseProjection ξ z
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      frequencyVector, mul_comm] using h
  have h := curlSymbolEnergy_lagrange ξ (transverseProjection ξ z)
  rw [hdot, norm_zero, zero_pow (by decide), sub_zero] at h
  rw [← h]
  unfold curlSymbolEnergy
  rw [transverseProjection_curlSymbol, transverseProjection_curlSymbol,
    transverseProjection_curlSymbol]

end Navier.Analysis.FourierTransverseProjection
