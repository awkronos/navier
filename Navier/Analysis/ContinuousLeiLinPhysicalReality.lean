import Navier.Analysis.ContinuousLeiLinPhysicalCarrier
import Navier.Analysis.ContinuousLeiLinReality
import Navier.Analysis.GalerkinFourierReality

/-!
# Real-valued physical coordinates from Hermitian Fourier profiles

This file discharges the Fourier-inversion part of the continuous Lei--Lin
reality route.  For an integrable coordinate of a Hermitian frequency profile,
the actual `physicalCoord` inverse Fourier integral is fixed by conjugation and
therefore has zero imaginary part.

The proof reuses `GalerkinFourierReality.scalar_inverse_fourier_real`, whose
change-of-variables argument is already stated for the same Euclidean Fourier
carrier.  The `Integrable` premise records the required coordinatewise `L¹`
input; later admissible-ball work must supply it for a fixed-point profile.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinPhysicalReality

open MeasureTheory
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinReality
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier

/-- An `L¹` coordinate of a Hermitian continuous Lei--Lin profile has an
inverse Fourier transform fixed by complex conjugation. -/
theorem physicalCoord_star_eq_self
    (w : ES → ComplexSpace) (hw : ProfileHermitian w)
    (i : Fin 3) (hi : Integrable (fun ξ : ES => w ξ i)) (x : ES) :
    star (physicalCoord w i x) = physicalCoord w i x := by
  exact (Navier.Analysis.GalerkinFourierReality.scalar_inverse_fourier_real
    (fun ξ : ES => w ξ i) hi (coordHermitian_of_profileHermitian hw i) x).2

/-- The same result in the form consumed by the physical velocity carrier:
the imaginary part of the actual `physicalCoord` value vanishes. -/
theorem physicalCoord_im_eq_zero
    (w : ES → ComplexSpace) (hw : ProfileHermitian w)
    (i : Fin 3) (hi : Integrable (fun ξ : ES => w ξ i)) (x : ES) :
    (physicalCoord w i x).im = 0 := by
  have hreal := physicalCoord_star_eq_self w hw i hi x
  have h := congrArg Complex.im hreal
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

end Navier.Analysis.ContinuousLeiLinPhysicalReality

#print axioms Navier.Analysis.ContinuousLeiLinPhysicalReality.physicalCoord_star_eq_self
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalReality.physicalCoord_im_eq_zero
