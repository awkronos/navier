import Navier.Analysis.ComplexLerayProjection

/-!
# Hermitian Euclidean norm bridge for the complex Leray projection

This file transports the coordinate-level complex Leray map to Mathlib's
canonical Hermitian Euclidean space.  At a real frequency, the transported map
is exactly the orthogonal star projection onto the complex plane perpendicular
to that frequency.  Norm contraction, Hermitian transversality, and
idempotence therefore follow from Mathlib's projection API, including at zero
frequency.

The Hermitian inner product is kept distinct from the bilinear Fourier
divergence.  They agree in the theorem below only because the frequency vector
has real coordinates.  No Fourier transform, Helmholtz decomposition, heat
semigroup, Duhamel estimate, or local solution is constructed here.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ComplexLerayNorm

open Navier
open Navier.Routes.R7
open Navier.Analysis.ComplexLerayProjection

/-- Complex Euclidean three-space with Mathlib's Hermitian inner product. -/
abbrev ComplexE3 := EuclideanSpace ℂ (Fin 3)

/-- Canonical coordinate transport to Hermitian Euclidean three-space. -/
def complexEuclideanPoint (z : ComplexSpace) : ComplexE3 :=
  WithLp.toLp 2 z

@[simp] theorem complexEuclideanPoint_apply
    (z : ComplexSpace) (i : Fin 3) :
    complexEuclideanPoint z i = z i :=
  rfl

/-- The Euclidean `ℓ²` norm of a complex coordinate vector. -/
def complexEuclideanNorm (z : ComplexSpace) : ℝ :=
  ‖complexEuclideanPoint z‖

/-- The real frequency embedded in complex Hermitian Euclidean space. -/
def complexFrequency (q : Space) : ComplexE3 :=
  complexEuclideanPoint (complexOfReal q)

@[simp] theorem complexFrequency_apply (q : Space) (i : Fin 3) :
    complexFrequency q i = (q i : ℂ) := by
  simp [complexFrequency, complexOfReal, complexOfParts]

@[simp] theorem complexFrequency_zero :
    complexFrequency 0 = 0 := by
  ext i
  simp

/-- The complex plane Hermitian-orthogonal to a real frequency. -/
def complexFrequencyPlane (q : Space) : Submodule ℂ ComplexE3 :=
  (ℂ ∙ complexFrequency q)ᗮ

/-- Canonical Hermitian orthogonal projection onto the complex frequency
plane. -/
def complexEuclideanLeray (q : Space) : ComplexE3 →L[ℂ] ComplexE3 :=
  (complexFrequencyPlane q).starProjection

theorem complexEuclideanLeray_mem (q : Space) (v : ComplexE3) :
    complexEuclideanLeray q v ∈ complexFrequencyPlane q :=
  Submodule.starProjection_apply_mem _ _

/-- Hermitian transversality of the canonical projection. -/
theorem inner_complexEuclideanLeray (q : Space) (v : ComplexE3) :
    inner ℂ (complexFrequency q) (complexEuclideanLeray q v) = 0 :=
  (Submodule.mem_orthogonal_singleton_iff_inner_right).1
    (complexEuclideanLeray_mem q v)

/-- The canonical complex orthogonal projection contracts the Hermitian
Euclidean norm. -/
theorem complexEuclideanLeray_norm_le (q : Space) (v : ComplexE3) :
    ‖complexEuclideanLeray q v‖ ≤ ‖v‖ :=
  Submodule.norm_starProjection_apply_le _ _

/-- The canonical complex orthogonal projection is idempotent. -/
theorem complexEuclideanLeray_idempotent (q : Space) (v : ComplexE3) :
    complexEuclideanLeray q (complexEuclideanLeray q v) =
      complexEuclideanLeray q v :=
  (Submodule.starProjection_eq_self_iff).2
    (complexEuclideanLeray_mem q v)

/-- For a real embedded frequency, Mathlib's Hermitian inner product is the
bilinear Fourier divergence coefficient. -/
theorem inner_complexFrequency (q : Space) (z : ComplexSpace) :
    inner ℂ (complexFrequency q) (complexEuclideanPoint z) =
      ∑ i, (q i : ℂ) * z i := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [complexFrequency, complexEuclideanPoint, complexOfReal,
    complexOfParts, dotProduct, mul_comm]

/-- The squared Hermitian norm of an embedded real frequency is its real
self-dot-product. -/
theorem complexFrequency_norm_sq (q : Space) :
    ‖complexFrequency q‖ ^ 2 = q ⬝ᵥ q := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [complexFrequency, complexEuclideanPoint, complexOfReal,
    complexOfParts, dotProduct, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Explicit formula for the canonical Hermitian orthogonal projection.  The
formula is total at zero frequency. -/
theorem complexEuclideanLeray_formula (q : Space) (v : ComplexE3) :
    complexEuclideanLeray q v =
      v -
        (inner ℂ (complexFrequency q) v /
          ((‖complexFrequency q‖ ^ 2 : ℝ) : ℂ)) •
            complexFrequency q := by
  change ((ℂ ∙ complexFrequency q)ᗮ).starProjection v = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  simp

/-- At zero frequency the canonical Hermitian projection is the identity. -/
@[simp] theorem complexEuclideanLeray_zero_frequency (v : ComplexE3) :
    complexEuclideanLeray 0 v = v := by
  rw [complexEuclideanLeray_formula]
  simp

/-- Split the real-frequency bilinear divergence into real and imaginary
polarizations. -/
theorem complexBilinearDot_parts (q : Space) (z : ComplexSpace) :
    ∑ i, (q i : ℂ) * z i =
      ((ComplexLerayProjection.realPart z ⬝ᵥ q : ℝ) : ℂ) +
        Complex.I *
          ((ComplexLerayProjection.imaginaryPart z ⬝ᵥ q : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [ComplexLerayProjection.realPart,
      ComplexLerayProjection.imaginaryPart, dotProduct, mul_comm]

/-- Division by a real scalar commutes with recombining real and imaginary
parts, including at a zero denominator. -/
theorem complex_division_of_parts (a b d : ℝ) :
    ((a / d : ℝ) : ℂ) + Complex.I * ((b / d : ℝ) : ℂ) =
      ((a : ℂ) + Complex.I * (b : ℂ)) / (d : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_div]
  ring

/-- Coordinate formula for the previously constructed complex-linear Leray
map. -/
theorem complexLeray_formula
    (q : Space) (z : ComplexSpace) (i : Fin 3) :
    complexLeray q z i =
      z i -
        ((∑ j, (q j : ℂ) * z j) / ((q ⬝ᵥ q : ℝ) : ℂ)) *
          (q i : ℂ) := by
  calc
    complexLeray q z i =
        complexOfParts
            (ComplexLerayProjection.realPart z)
            (ComplexLerayProjection.imaginaryPart z) i -
          (((ComplexLerayProjection.realPart z ⬝ᵥ q) /
              (q ⬝ᵥ q) : ℝ) : ℂ) * (q i : ℂ) -
          Complex.I *
            ((((ComplexLerayProjection.imaginaryPart z ⬝ᵥ q) /
                (q ⬝ᵥ q) : ℝ) : ℂ) * (q i : ℂ)) := by
      simp [complexLeray, complexOfParts, normalizedLeraySymbol]
      ring
    _ = complexOfParts
            (ComplexLerayProjection.realPart z)
            (ComplexLerayProjection.imaginaryPart z) i -
          ((((ComplexLerayProjection.realPart z ⬝ᵥ q) /
                (q ⬝ᵥ q) : ℝ) : ℂ) +
            Complex.I *
              (((ComplexLerayProjection.imaginaryPart z ⬝ᵥ q) /
                  (q ⬝ᵥ q) : ℝ) : ℂ)) * (q i : ℂ) := by
      ring
    _ = z i -
          ((((ComplexLerayProjection.realPart z ⬝ᵥ q : ℝ) : ℂ) +
              Complex.I *
                ((ComplexLerayProjection.imaginaryPart z ⬝ᵥ q : ℝ) : ℂ)) /
            ((q ⬝ᵥ q : ℝ) : ℂ)) * (q i : ℂ) := by
      rw [complex_division_of_parts]
      rw [congrFun (complexOfParts_real_imaginary z) i]
    _ = z i -
          ((∑ j, (q j : ℂ) * z j) /
            ((q ⬝ᵥ q : ℝ) : ℂ)) * (q i : ℂ) := by
      rw [complexBilinearDot_parts]

/-- The coordinate complex Leray map is exactly Mathlib's canonical Hermitian
star projection after Euclidean transport.  No nonzero-frequency hypothesis is
needed. -/
theorem complexEuclideanPoint_complexLeray
    (q : Space) (z : ComplexSpace) :
    complexEuclideanPoint (complexLeray q z) =
      complexEuclideanLeray q (complexEuclideanPoint z) := by
  rw [complexEuclideanLeray_formula]
  ext i
  change complexLeray q z i = z i - _
  rw [complexLeray_formula]
  simp [inner_complexFrequency, complexFrequency_norm_sq]

/-- The complex coordinate Leray map contracts the Hermitian Euclidean norm. -/
theorem complexEuclideanNorm_complexLeray_le
    (q : Space) (z : ComplexSpace) :
    complexEuclideanNorm (complexLeray q z) ≤
      complexEuclideanNorm z := by
  rw [complexEuclideanNorm, complexEuclideanPoint_complexLeray]
  exact complexEuclideanLeray_norm_le _ _

/-- Hermitian transversality transported back to the coordinate complex Leray
map. -/
theorem complexLeray_hermitian_transverse
    (q : Space) (z : ComplexSpace) :
    inner ℂ (complexFrequency q)
      (complexEuclideanPoint (complexLeray q z)) = 0 := by
  rw [complexEuclideanPoint_complexLeray]
  exact inner_complexEuclideanLeray _ _

/-- Bilinear Fourier transversality recovered from the distinct Hermitian
statement using the real-frequency bridge. -/
theorem complexLeray_bilinear_transverse_smoke
    (q : Space) (z : ComplexSpace) :
    ∑ i, (q i : ℂ) * complexLeray q z i = 0 := by
  rw [← inner_complexFrequency]
  exact complexLeray_hermitian_transverse _ _

/-- The Euclidean coordinate transport is injective. -/
theorem complexEuclideanPoint_injective :
    Function.Injective complexEuclideanPoint :=
  WithLp.toLp_injective 2

/-- Idempotence recovered through the canonical Hermitian star projection
rather than by reusing the coordinate-level theorem. -/
theorem complexLeray_idempotent_smoke (q : Space) (z : ComplexSpace) :
    complexLeray q (complexLeray q z) = complexLeray q z := by
  apply complexEuclideanPoint_injective
  rw [complexEuclideanPoint_complexLeray,
    complexEuclideanPoint_complexLeray,
    complexEuclideanLeray_idempotent]

end Navier.Analysis.ComplexLerayNorm
