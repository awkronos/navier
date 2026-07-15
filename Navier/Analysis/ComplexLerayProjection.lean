import Navier.Analysis.LerayProjection

/-!
# Complex frequencywise Leray projection

This file canonically extends the checked real normalized Leray symbol to
complex Fourier coefficients by applying it independently to real and
imaginary polarizations.  The extension is packaged as a complex-linear map.
It is totalized to the identity at zero frequency, commutes with conjugation,
is idempotent, and has vanishing complex bilinear divergence against its real
frequency.

The transversality and idempotence proofs are transported from the canonical
Euclidean orthogonal projection in `Navier.Analysis.LerayProjection`.  This is
still frequencywise finite-dimensional algebra: it does not construct a
Fourier transform, Helmholtz decomposition, heat semigroup, Duhamel estimate,
or local Navier--Stokes solution.  A contraction theorem for the Hermitian
Euclidean norm is left as a separate representation bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ComplexLerayProjection

open Navier
open Navier.Routes.R7
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.LerayProjection

/-- Complex three-space in the repository's coordinate representation. -/
abbrev ComplexSpace := Fin 3 → ℂ

/-- Coordinatewise real polarization of a complex vector. -/
def realPart (z : ComplexSpace) : Space :=
  fun i ↦ (z i).re

/-- Coordinatewise imaginary polarization of a complex vector. -/
def imaginaryPart (z : ComplexSpace) : Space :=
  fun i ↦ (z i).im

/-- Recombine real and imaginary polarizations into a complex vector. -/
def complexOfParts (x y : Space) : ComplexSpace :=
  fun i ↦ (x i : ℂ) + Complex.I * (y i : ℂ)

/-- The canonical coordinatewise inclusion of real vectors into complex
vectors. -/
def complexOfReal (x : Space) : ComplexSpace :=
  complexOfParts x 0

/-- Coordinatewise complex conjugation. -/
def complexConjugate (z : ComplexSpace) : ComplexSpace :=
  fun i ↦ starRingEnd ℂ (z i)

@[simp] theorem complexOfParts_apply (x y : Space) (i : Fin 3) :
    complexOfParts x y i = (x i : ℂ) + Complex.I * (y i : ℂ) :=
  rfl

@[simp] theorem complexOfParts_re (x y : Space) :
    realPart (complexOfParts x y) = x := by
  ext i
  simp [realPart, complexOfParts]

@[simp] theorem complexOfParts_im (x y : Space) :
    imaginaryPart (complexOfParts x y) = y := by
  ext i
  simp [imaginaryPart, complexOfParts]

/-- Real and imaginary polarization loses no complex coordinate data. -/
theorem complexOfParts_real_imaginary (z : ComplexSpace) :
    complexOfParts (realPart z) (imaginaryPart z) = z := by
  ext i
  apply Complex.ext <;>
    simp [complexOfParts, realPart, imaginaryPart]

@[simp] theorem realPart_add (z w : ComplexSpace) :
    realPart (z + w) = realPart z + realPart w := by
  ext i
  simp [realPart]

@[simp] theorem imaginaryPart_add (z w : ComplexSpace) :
    imaginaryPart (z + w) = imaginaryPart z + imaginaryPart w := by
  ext i
  simp [imaginaryPart]

@[simp] theorem realPart_smul (a : ℂ) (z : ComplexSpace) :
    realPart (a • z) = a.re • realPart z - a.im • imaginaryPart z := by
  ext i
  simp [realPart, imaginaryPart, Complex.mul_re]

@[simp] theorem imaginaryPart_smul (a : ℂ) (z : ComplexSpace) :
    imaginaryPart (a • z) = a.re • imaginaryPart z + a.im • realPart z := by
  ext i
  simp [realPart, imaginaryPart, Complex.mul_im]

@[simp] theorem realPart_complexConjugate (z : ComplexSpace) :
    realPart (complexConjugate z) = realPart z := by
  ext i
  simp [realPart, complexConjugate]

@[simp] theorem imaginaryPart_complexConjugate (z : ComplexSpace) :
    imaginaryPart (complexConjugate z) = -imaginaryPart z := by
  ext i
  simp [imaginaryPart, complexConjugate]

/-- The checked real normalized Leray symbol is additive in its
polarization. -/
theorem normalizedLeraySymbol_add (q v w : Space) :
    normalizedLeraySymbol q (v + w) =
      normalizedLeraySymbol q v + normalizedLeraySymbol q w := by
  ext i
  simp [normalizedLeraySymbol, add_dotProduct]
  ring

/-- The checked real normalized Leray symbol preserves subtraction. -/
theorem normalizedLeraySymbol_sub (q v w : Space) :
    normalizedLeraySymbol q (v - w) =
      normalizedLeraySymbol q v - normalizedLeraySymbol q w := by
  ext i
  simp [normalizedLeraySymbol, sub_dotProduct]
  ring

/-- The checked real normalized Leray symbol is real homogeneous. -/
theorem normalizedLeraySymbol_smul (q v : Space) (a : ℝ) :
    normalizedLeraySymbol q (a • v) =
      a • normalizedLeraySymbol q v := by
  ext i
  simp [normalizedLeraySymbol, smul_dotProduct]
  ring

@[simp] theorem normalizedLeraySymbol_neg (q v : Space) :
    normalizedLeraySymbol q (-v) = -normalizedLeraySymbol q v := by
  simpa only [neg_one_smul] using
    normalizedLeraySymbol_smul q v (-1)

@[simp] theorem normalizedLeraySymbol_zero_vector (q : Space) :
    normalizedLeraySymbol q 0 = 0 := by
  simpa only [zero_smul] using
    normalizedLeraySymbol_smul q 0 0

/-- The real normalized symbol is transverse to its frequency.  This is a
coordinate transport of the canonical Euclidean star projection theorem. -/
theorem normalizedLeraySymbol_transverse (q v : Space) :
    q ⬝ᵥ normalizedLeraySymbol q v = 0 := by
  have h := inner_euclideanLeray
    (officialEuclideanPoint q) (officialEuclideanPoint v)
  rw [← officialPoint_normalizedLeray,
    officialPoint_inner_eq_dotProduct] at h
  simpa [dotProduct_comm] using h

/-- The real normalized symbol is idempotent, transported from the canonical
Euclidean orthogonal projection. -/
theorem normalizedLeraySymbol_idempotent (q v : Space) :
    normalizedLeraySymbol q (normalizedLeraySymbol q v) =
      normalizedLeraySymbol q v := by
  ext i
  have h := congrArg
    (fun x : EuclideanSpace ℝ (Fin 3) ↦ x i)
    (euclideanLeray_idempotent
      (officialEuclideanPoint q) (officialEuclideanPoint v))
  simpa [← officialPoint_normalizedLeray] using h

/-- Canonical complex-linear extension of the checked real normalized Leray
symbol at a real frequency. -/
def complexLeray (q : Space) : ComplexSpace →ₗ[ℂ] ComplexSpace where
  toFun z :=
    complexOfParts
      (normalizedLeraySymbol q (realPart z))
      (normalizedLeraySymbol q (imaginaryPart z))
  map_add' z w := by
    ext i
    apply Complex.ext <;>
      simp [complexOfParts, normalizedLeraySymbol_add]
  map_smul' a z := by
    ext i
    apply Complex.ext <;>
      simp [complexOfParts, normalizedLeraySymbol_add,
        normalizedLeraySymbol_sub, normalizedLeraySymbol_smul]

@[simp] theorem complexLeray_apply
    (q : Space) (z : ComplexSpace) (i : Fin 3) :
    complexLeray q z i =
      (normalizedLeraySymbol q (realPart z) i : ℂ) +
        Complex.I *
          (normalizedLeraySymbol q (imaginaryPart z) i : ℂ) :=
  rfl

/-- The complex extension acts on the real polarization by the checked real
symbol. -/
@[simp] theorem complexLeray_re (q : Space) (z : ComplexSpace) :
    realPart (complexLeray q z) =
      normalizedLeraySymbol q (realPart z) := by
  ext i
  simp [realPart]

/-- The complex extension acts on the imaginary polarization by the checked
real symbol. -/
@[simp] theorem complexLeray_im (q : Space) (z : ComplexSpace) :
    imaginaryPart (complexLeray q z) =
      normalizedLeraySymbol q (imaginaryPart z) := by
  ext i
  simp [imaginaryPart]

/-- On an embedded real polarization, the complex extension is exactly the
embedded checked real symbol. -/
theorem complexLeray_ofReal (q v : Space) :
    complexLeray q (complexOfReal v) =
      complexOfReal (normalizedLeraySymbol q v) := by
  ext i
  simp [complexOfReal, complexOfParts]

/-- Zero frequency is totalized by the identity map. -/
@[simp] theorem complexLeray_zero_frequency (z : ComplexSpace) :
    complexLeray 0 z = z := by
  ext i
  apply Complex.ext <;>
    simp [complexLeray, complexOfParts, normalizedLeraySymbol_zero,
      realPart, imaginaryPart]

/-- The real-frequency complex Leray map commutes with coordinatewise complex
conjugation. -/
theorem complexLeray_conjugate (q : Space) (z : ComplexSpace) :
    complexLeray q (complexConjugate z) =
      complexConjugate (complexLeray q z) := by
  ext i
  apply Complex.ext <;>
    simp [complexLeray, complexOfParts, complexConjugate]

/-- The complex Leray map is frequencywise idempotent. -/
theorem complexLeray_idempotent (q : Space) (z : ComplexSpace) :
    complexLeray q (complexLeray q z) = complexLeray q z := by
  ext i
  apply Complex.ext <;>
    simp [complexLeray, complexOfParts,
      normalizedLeraySymbol_idempotent]

/-- Bilinear Fourier divergence vanishes after projection.  Because the
frequency is real, this is distinct in statement from a generic Hermitian
inner-product identity. -/
theorem complexLeray_transverse (q : Space) (z : ComplexSpace) :
    ∑ i, (q i : ℂ) * complexLeray q z i = 0 := by
  apply Complex.ext
  · simp [complexLeray, complexOfParts]
    simpa only [dotProduct] using
      normalizedLeraySymbol_transverse q (realPart z)
  · simp [complexLeray, complexOfParts]
    simpa only [dotProduct] using
      normalizedLeraySymbol_transverse q (imaginaryPart z)

end Navier.Analysis.ComplexLerayProjection
