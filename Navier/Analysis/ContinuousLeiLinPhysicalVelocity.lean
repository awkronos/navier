import Navier.Analysis.ContinuousLeiLinPhysicalReality

/-!
# The real physical velocity carrier of the whole-space Lei--Lin profile

Pointwise-PDE obligation 5 (`NOTES-ns5-20260912.md`, §"EXACT remaining
obligations"): invert the Hermitian symmetry `w (-ξ) = conj (w ξ)` through
`𝓕⁻` and produce an honestly **real-valued** physical velocity coordinate.

Two things happen here that the existing reality layer does not do.

**A live premise is removed.**  `GalerkinFourierReality.scalar_inverse_fourier_real`
and therefore `ContinuousLeiLinPhysicalReality.physicalCoord_star_eq_self` /
`physicalCoord_im_eq_zero` all carry an `Integrable (fun ξ => w ξ i)`
hypothesis.  That hypothesis is not needed: conjugation commutes with the
Bochner integral unconditionally (`MeasureTheory.integral_conj`), the
substitution `v ↦ -v` is the volume measure's negation invariance
(`MeasureTheory.Measure.measurePreserving_neg`, the device already used by
`ContinuousLeiLinReality.coordHermitian_convolution_mul`), and in the
Bochner-junk case both sides are `0`.  `star_fourierInv_of_coordHermitian`
below is the premise-free statement; the profile forms follow.  The earlier
conditional statements are kept intact for their existing consumer
(`ContinuousLeiLinPhysicalIntegrability.physicalCoord_im_eq_zero_of_Xm1_X1`).

**A carrier is constructed, not merely a property proved.**
`realPhysicalCoord` is a genuine `ES → ℝ` velocity coordinate;
`ofReal_realPhysicalCoord` certifies that for a Hermitian profile it loses
nothing, `sum_abs_realPhysicalCoord_le_coordinateX0Mass` gives it the Wiener
slot bound the admissible-ball estimates control, and
`ofReal_realPhysicalCoord_continuousMildImage` transports reality along one
Picard step via `ContinuousLeiLinReality.continuousMildImage_neg`, so the
eventual admissible fixed point inverts to a real velocity field.

**The field has the shape the crown interface consumes.**  `physicalVelocity`
is a `Navier.VelocityEvolution`, i.e. `ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)`, the
exact type `SolvesBefore`/`SatisfiesNavierStokes`/`Incompressible` quantify
over; `physicalVelocity_fourierDatum` discharges the *initial* clause against a
Schwartz datum, and `norm_physicalVelocity_le_coordinateX0Mass` gives the
pointwise sup bound in the physical sup norm.  The remaining pointwise
obligations are therefore now statements about a concrete constructed object.

## What this file deliberately does NOT claim

* No PDE.  The pointwise time derivative under `𝓕⁻`, the Laplacian (obligation
  2, which needs `‖ξ‖^k` moments from heat smoothing) and the pressure
  reconstruction (obligation 3) remain open and are untouched here.
* No fixed point.  `continuousMildImage` is applied to an arbitrary Hermitian
  trajectory; the admissible-ball completeness primitive (brick (a)) is
  unaffected.
* No smoothness, decay or continuity of `realPhysicalCoord` beyond the
  pointwise `coordinateX0Mass` bound inherited from the inversion estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinPhysicalVelocity

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace BigOperators
open Navier.Analysis.ContinuousLeiLinSpace (ES ComplexSpace)
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
  (physicalCoord norm_physicalCoord_le sum_norm_physicalCoord_le_coordinateX0Mass)
open Navier.Analysis.ContinuousLeiLinReality
  (ProfileHermitian CoordHermitian coordHermitian_of_profileHermitian
    continuousMildImage_neg)

/-! ## Reality of the inverse Fourier integral -/

/-- **The inverse Fourier integral of a Hermitian scalar profile is real.**
Unconditional: the negation substitution and `integral_conj` both hold for the
Bochner junk value as well. -/
theorem star_fourierInv_of_coordHermitian (f : ES → ℂ) (hf : CoordHermitian f)
    (x : ES) : star (𝓕⁻ f x) = 𝓕⁻ f x := by
  have hpres : MeasurePreserving (Neg.neg : ES → ES) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (Neg.neg : ES → ES) :=
    (MeasurableEquiv.neg ES).measurableEmbedding
  have hrep : 𝓕⁻ f x = ∫ v : ES,
      Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v := by
    rw [Real.fourierInv_eq' f x]
    simp only [smul_eq_mul]
  have hEneg (v : ES) :
      Complex.exp ((↑(2 * Real.pi * (⟪(-v), x⟫ : ℝ)) : ℂ) * Complex.I)
        = star (Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I)) := by
    have hinner : (⟪(-v), x⟫ : ℝ) = -(⟪v, x⟫ : ℝ) := inner_neg_left _ _
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, hinner]
    push_cast
    ring
  have hpt (v : ES) :
      Complex.exp ((↑(2 * Real.pi * (⟪(-v), x⟫ : ℝ)) : ℂ) * Complex.I) * f (-v)
        = star (Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v) := by
    rw [hEneg v, hf v, star_mul']
  have hkey : 𝓕⁻ f x = star (𝓕⁻ f x) := by
    calc 𝓕⁻ f x = ∫ v : ES,
          Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v := hrep
      _ = ∫ v : ES,
          Complex.exp ((↑(2 * Real.pi * (⟪(-v), x⟫ : ℝ)) : ℂ) * Complex.I) * f (-v) :=
          (hpres.integral_comp hemb (fun v : ES =>
            Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v)).symm
      _ = ∫ v : ES, star
          (Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = star (∫ v : ES,
          Complex.exp ((↑(2 * Real.pi * (⟪v, x⟫ : ℝ)) : ℂ) * Complex.I) * f v) :=
          integral_conj
      _ = star (𝓕⁻ f x) := by rw [← hrep]
  exact hkey.symm

/-- The physical coordinate of a Hermitian profile is fixed by `star`. -/
theorem star_physicalCoord_of_profileHermitian {w : ES → ComplexSpace}
    (hw : ProfileHermitian w) (i : Fin 3) (x : ES) :
    star (physicalCoord w i x) = physicalCoord w i x :=
  star_fourierInv_of_coordHermitian (fun ξ : ES => w ξ i)
    (coordHermitian_of_profileHermitian hw i) x

/-- The physical coordinate of a Hermitian profile has vanishing imaginary
part. -/
theorem im_physicalCoord_of_profileHermitian {w : ES → ComplexSpace}
    (hw : ProfileHermitian w) (i : Fin 3) (x : ES) :
    (physicalCoord w i x).im = 0 := by
  have h := star_physicalCoord_of_profileHermitian hw i x
  rw [Complex.star_def, Complex.ext_iff] at h
  have him := h.2
  rw [Complex.conj_im] at him
  linarith

/-! ## The real physical velocity coordinate -/

/-- **The real physical velocity coordinate.**  This is the carrier the
pointwise `SatisfiesNavierStokes` obligation consumes: a genuine real-valued
function on physical space, defined for every profile (the real part is total)
and *faithful* exactly on Hermitian profiles, by
`ofReal_realPhysicalCoord` below. -/
def realPhysicalCoord (w : ES → ComplexSpace) (i : Fin 3) : ES → ℝ :=
  fun x => (physicalCoord w i x).re

/-- **No information is lost**: for a Hermitian profile the real coordinate
carries the whole complex physical coordinate. -/
theorem ofReal_realPhysicalCoord {w : ES → ComplexSpace}
    (hw : ProfileHermitian w) (i : Fin 3) (x : ES) :
    ((realPhysicalCoord w i x : ℝ) : ℂ) = physicalCoord w i x := by
  apply Complex.ext
  · simp [realPhysicalCoord]
  · simp [realPhysicalCoord, im_physicalCoord_of_profileHermitian hw i x]

/-- The real coordinate inherits the pointwise Wiener-slot bound of the complex
one; no Hermitian hypothesis is needed because `|re z| ≤ ‖z‖`. -/
theorem abs_realPhysicalCoord_le (w : ES → ComplexSpace) (i : Fin 3) (x : ES) :
    |realPhysicalCoord w i x| ≤ ∫ ξ : ES, ‖w ξ i‖ :=
  le_trans (by simpa [realPhysicalCoord] using
      RCLike.abs_re_le_norm (K := ℂ) (physicalCoord w i x))
    (norm_physicalCoord_le w i x)

/-- The full real velocity vector at a physical point is dominated by the
carrier's `coordinateX0Mass`. -/
theorem sum_abs_realPhysicalCoord_le_coordinateX0Mass (w : ES → ComplexSpace)
    (x : ES) :
    ∑ i : Fin 3, |realPhysicalCoord w i x| ≤
      Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateX0Mass w :=
  le_trans (Finset.sum_le_sum fun i _ => by
      simpa [realPhysicalCoord] using
        RCLike.abs_re_le_norm (K := ℂ) (physicalCoord w i x))
    (sum_norm_physicalCoord_le_coordinateX0Mass w x)

/-! ## Transport along the mild map -/

/-- **The mild image inverts to a real velocity coordinate.**  Combining
`ContinuousLeiLinReality.continuousMildImage_neg` (the mild map preserves
Hermitian symmetry) with the inversion fact above: every Hermitian trajectory
is mapped by one Picard step to a profile whose physical inversion is real.
At the eventual fixed point this is the reality of the constructed velocity. -/
theorem ofReal_realPhysicalCoord_continuousMildImage (ν : ℝ) (hν : 0 < ν)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace)
    (ha : ProfileHermitian a) (hu : ∀ s : ℝ, ProfileHermitian (u s))
    (t : ℝ) (i : Fin 3) (x : ES) :
    ((realPhysicalCoord
        (Navier.Analysis.ContinuousLeiLinSelfMap.continuousMildImage
          ν hν a u t) i x : ℝ) : ℂ)
      = physicalCoord
          (Navier.Analysis.ContinuousLeiLinSelfMap.continuousMildImage
            ν hν a u t) i x :=
  ofReal_realPhysicalCoord (continuousMildImage_neg ν hν a u ha hu t) i x

/-! ## The `VelocityEvolution`-shaped field and its initial datum -/

/-- The Euclidean point corresponding to a standard-coordinate point of
`Navier.Space`; the inverse of the `FourierMajorant` carrier projection
`spaceProj`. -/
def euclidPoint (x : Navier.Space) : ES := (WithLp.toLp 2 x)

@[simp] theorem spaceProj_euclidPoint (x : Navier.Space) :
    Navier.Analysis.FourierMajorant.spaceProj (euclidPoint x) = x := rfl

/-- **The physical velocity evolution of a frequency trajectory.**  This has
exactly the `Navier.VelocityEvolution` shape that `SolvesBefore`,
`SatisfiesNavierStokes` and `Incompressible` consume, so the remaining
pointwise obligations are now statements about a concrete object rather than
about a missing one. -/
def physicalVelocity (w : ℝ → ES → ComplexSpace) : Navier.VelocityEvolution :=
  fun t x i => realPhysicalCoord (w t) i (euclidPoint x)

/-- Faithfulness of the physical velocity evolution at a Hermitian
trajectory. -/
theorem ofReal_physicalVelocity {w : ℝ → ES → ComplexSpace}
    (hw : ∀ t : ℝ, ProfileHermitian (w t)) (t : ℝ) (x : Navier.Space)
    (i : Fin 3) :
    ((physicalVelocity w t x i : ℝ) : ℂ) = physicalCoord (w t) i (euclidPoint x) :=
  ofReal_realPhysicalCoord (hw t) i (euclidPoint x)

/-- **Physical initial agreement.**  Inverting the Fourier datum of a Schwartz
velocity returns the initial velocity itself, in `Navier.Space` coordinates.
This is the initial clause the local-existence interface requires of the
constructed field. -/
theorem physicalVelocity_fourierDatum (u₀ : Navier.SchwartzVelocity)
    (w : ℝ → ES → ComplexSpace) (t : ℝ)
    (hw : w t = Navier.Analysis.ContinuousLeiLinPhysicalCarrier.fourierDatum u₀)
    (x : Navier.Space) (i : Fin 3) :
    physicalVelocity w t x i = u₀ x i := by
  have h := Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord_fourierDatum
    u₀ i (euclidPoint x)
  simp only [physicalVelocity, realPhysicalCoord, hw, h, spaceProj_euclidPoint,
    Complex.ofReal_re]

/-- The physical velocity is bounded at every point by the carrier's Wiener
slot mass — the quantity the admissible ball controls. -/
theorem norm_physicalVelocity_le_coordinateX0Mass (w : ℝ → ES → ComplexSpace)
    (t : ℝ) (x : Navier.Space) :
    ‖physicalVelocity w t x‖ ≤
      Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateX0Mass (w t) := by
  have hnn : (0 : ℝ) ≤
      Navier.Analysis.ContinuousLeiLinTimeDuhamel.coordinateX0Mass (w t) :=
    le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (sum_abs_realPhysicalCoord_le_coordinateX0Mass (w t) (euclidPoint x))
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_
  have hi : |realPhysicalCoord (w t) i (euclidPoint x)| ≤
      ∑ j : Fin 3, |realPhysicalCoord (w t) j (euclidPoint x)| :=
    Finset.single_le_sum
      (f := fun j : Fin 3 => |realPhysicalCoord (w t) j (euclidPoint x)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact le_trans hi (sum_abs_realPhysicalCoord_le_coordinateX0Mass (w t)
    (euclidPoint x))

end Navier.Analysis.ContinuousLeiLinPhysicalVelocity

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.star_fourierInv_of_coordHermitian
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.star_physicalCoord_of_profileHermitian
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.im_physicalCoord_of_profileHermitian
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.ofReal_realPhysicalCoord
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.abs_realPhysicalCoord_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.sum_abs_realPhysicalCoord_le_coordinateX0Mass
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.ofReal_realPhysicalCoord_continuousMildImage
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.spaceProj_euclidPoint
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.ofReal_physicalVelocity
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.physicalVelocity_fourierDatum
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.norm_physicalVelocity_le_coordinateX0Mass
