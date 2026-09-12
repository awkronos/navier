import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Navier.Analysis.ContinuousLeiLinDissipation
import Navier.Analysis.ContinuousLeiLinSelfMap
import Navier.Routes.R7.FiniteReality
import Mathlib.Analysis.Convolution

/-!
# Hermitian reality and frequency transversality of the continuous mild map

Brick (c), first missing objects (`NOTES-ns.md` §NS4.3, `NOTES-ns5-20260912.md`).
The physical velocity is recovered coordinatewise by `physicalCoord = 𝓕⁻ ∘ coord`
(`ContinuousLeiLinPhysicalCarrier`); it is real-valued exactly when each carrier
profile satisfies the Hermitian symmetry `w (-ξ) = conj (w ξ)`.  This file proves

* `ProfileHermitian` is preserved by `heatVec`, by the scalar convolution against
  `ContinuousLinearMap.mul ℂ ℂ` (the substitution `t = -s` in the Bochner
  integral uses the volume measure's negation invariance —
  `MeasureTheory.Measure.measurePreserving_neg` with the `IsNegInvariant volume`
  instance on `EuclideanSpace ℝ (Fin 3)`, which resolves by `inferInstance`
  because finite-dimensional volume is an inner-regular additive Haar measure;
  the instance is `to_additive`-generated and therefore invisible to source
  grep, so it was verified by compilation probe, not by text search), hence by
  `rawNavierConvection` (which is *anti*-Hermitian: the output-frequency
  prefactor contributes the sign), by the Leray-dressed
  `continuousNavierBilinear` (the `Complex.I` phase conjugates the sign back,
  and the Leray multiplier is even in the frequency and commutes with
  conjugation), by `continuousNavierSource`, by `continuousDuhamel` (the Bochner
  integral commutes with conjugation pointwise in time via the unconditional
  `integral_conj`), and therefore by `continuousMildImage`;
* `ProfileDivergenceFree` — the frequency-space transversality
  `∑ i, (spaceProj ξ i : ℂ) * w ξ i = 0`, i.e. the Fourier image of the
  incompressibility clause consumed later by the pointwise `Incompressible`
  obligation — holds for the Duhamel term by `complexLeray_transverse` at the
  output frequency, is preserved by the heat term (the heat multiplier is a
  scalar and the datum's transversality is transported), and therefore holds
  for the mild image of a divergence-free datum, *provided* the time integrands
  are integrable on `[0,t]`.  That hypothesis is carried explicitly: without it
  a dot product of coordinate Bochner integrals need not equal the integral of
  the pointwise dot product (the junk-value case is genuinely different), and
  the admissible-ball estimates are the intended supplier.

## What this file deliberately does NOT claim

* No pointwise PDE identity yet: reality + transversality of the mild image are
  the *first* missing objects on the `SatisfiesNavierStokes`/`Incompressible`
  route; the time derivative, the Laplacian (heat smoothing supplies the extra
  decay), and the pressure reconstruction remain separate obligations.
* No integrability of the Duhamel time integrands: that is a hypothesis here,
  to be discharged at the fixed point from the ball's mixed-`X¹` estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinReality

open MeasureTheory Set
open scoped BigOperators Convolution
open Navier
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ComplexLerayProjection
  (complexConjugate complexLeray complexLeray_conjugate complexLeray_transverse)
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Routes.R7 (complexLeray_neg_frequency)

/-! ## The symmetry predicates -/

/-- Hermitian (reality) symmetry of a frequency-space vector profile:
`w (-ξ) = conj (w ξ)` coordinatewise.  Fourier inversion of a Hermitian
profile is real-valued. -/
def ProfileHermitian (w : ES → ComplexSpace) : Prop :=
  ∀ ξ : ES, w (-ξ) = complexConjugate (w ξ)

/-- Scalar Hermitian symmetry: `f (-ξ) = star (f ξ)`.  This is the coordinate
form of `ProfileHermitian`. -/
def CoordHermitian (f : ES → ℂ) : Prop :=
  ∀ ξ : ES, f (-ξ) = star (f ξ)

/-- Frequency transversality of a vector profile: at every frequency the
complex dot product of the (real) frequency with the value vanishes.  This is
the Fourier-side image of the incompressibility clause. -/
def ProfileDivergenceFree (w : ES → ComplexSpace) : Prop :=
  ∀ ξ : ES, ∑ i : Fin 3, (spaceProj ξ i : ℂ) * w ξ i = 0

theorem complexConjugate_apply (z : ComplexSpace) (i : Fin 3) :
    complexConjugate z i = star (z i) :=
  (congrFun Complex.star_def (z i)).symm

theorem complexConjugate_add (z w : ComplexSpace) :
    complexConjugate (z + w) = complexConjugate z + complexConjugate w := by
  ext i
  simp only [complexConjugate_apply, Pi.add_apply, star_add]

theorem coordHermitian_of_profileHermitian {w : ES → ComplexSpace}
    (h : ProfileHermitian w) (i : Fin 3) : CoordHermitian (fun ξ => w ξ i) := by
  intro ξ
  show w (-ξ) i = star (w ξ i)
  rw [h ξ, complexConjugate_apply]

theorem profileHermitian_of_coordHermitian {w : ES → ComplexSpace}
    (h : ∀ i : Fin 3, CoordHermitian (fun ξ => w ξ i)) : ProfileHermitian w := by
  intro ξ
  ext i
  rw [complexConjugate_apply]
  exact h i ξ

/-! ## The heat factors preserve Hermitian symmetry -/

/-- The scalar heat multiplier is real and even in the frequency, so it
preserves Hermitian symmetry. -/
theorem coordHermitian_heatMode (f : ES → ℂ) (h : CoordHermitian f) (ν t : ℝ) :
    CoordHermitian (heatMode ν t f) := by
  intro ξ
  simp only [heatMode, norm_neg, h ξ, star_mul', Complex.star_def, Complex.conj_ofReal]

/-- The coordinatewise heat flow preserves profile Hermitian symmetry. -/
theorem profileHermitian_heatVec (a : ES → ComplexSpace) (h : ProfileHermitian a)
    (ν t : ℝ) : ProfileHermitian (heatVec ν t a) := by
  intro ξ
  ext i
  have hc := coordHermitian_heatMode (fun ζ => a ζ i)
    (coordHermitian_of_profileHermitian h i) ν t
  show heatMode ν t (fun ζ => a ζ i) (-ξ) = star (heatMode ν t (fun ζ => a ζ i) ξ)
  exact hc ξ

/-! ## The convolution preserves Hermitian symmetry -/

/-- **Hermitian symmetry of the scalar convolution.**  For `f, g : ES → ℂ` with
`f (-ξ) = conj (f ξ)` and likewise `g`, the convolution
`∫ t, f t * g (ξ - t)` is again Hermitian.  The substitution `t = -s` is the
volume-preserving negation map (`measurePreserving_neg` with the
`IsNegInvariant volume` instance — see the module header for why this was
probed rather than grepped); conjugation exits the integral by the
unconditional `integral_conj`.  The convolution unfolds to the bare integral at
`rfl` (both sides are defeq through `ContinuousLinearMap.mul`; the endpoint
equations are therefore written `rfl` rather than `convolution_def`, whose
higher-order `L` pattern does not unify against the `*`-form syntactically). -/
theorem coordHermitian_convolution_mul (f g : ES → ℂ) (hf : CoordHermitian f)
    (hg : CoordHermitian g) :
    CoordHermitian (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) := by
  intro ξ
  have hpres : MeasurePreserving (Neg.neg : ES → ES) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (Neg.neg : ES → ES) :=
    (MeasurableEquiv.neg ES).measurableEmbedding
  have hneg (s : ES) : -ξ - (-s) = -(ξ - s) := by
    simp only [sub_eq_add_neg, neg_neg, neg_add]
  have hpt (s : ES) : f (-s) * g (-ξ - (-s)) = star (f s * g (ξ - s)) := by
    rw [hneg, hf, hg, star_mul']
  exact calc (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) (-ξ)
      = ∫ t : ES, f t * g (-ξ - t) ∂volume := rfl
    _ = ∫ s : ES, f (-s) * g (-ξ - (-s)) ∂volume :=
        (hpres.integral_comp hemb (fun t => f t * g (-ξ - t))).symm
    _ = ∫ s : ES, star (f s * g (ξ - s)) ∂volume :=
        integral_congr_ae (ae_of_all volume fun s => hpt s)
    _ = star (∫ s : ES, f s * g (ξ - s) ∂volume) := integral_conj
    _ = star ((f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ) :=
        (congrArg star (rfl : (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ
          = ∫ t : ES, f t * g (ξ - t) ∂volume)).symm

/-! ## The bilinear symbol and the mild map -/

/-- The raw continuous Fourier convection tensor is *anti*-Hermitian: at the
negated frequency the output-frequency prefactor contributes exactly the sign
that conjugation of the (Hermitian) convolution does not. -/
theorem rawNavierConvection_neg (u v : ES → ComplexSpace) (hu : ProfileHermitian u)
    (hv : ProfileHermitian v) (ξ : ES) :
    rawNavierConvection u v (-ξ) = -(complexConjugate (rawNavierConvection u v ξ)) := by
  have hc (j : Fin 3) : CoordHermitian (fun η => u η j) :=
    coordHermitian_of_profileHermitian hu j
  have hd (i : Fin 3) : CoordHermitian (fun η => v η i) :=
    coordHermitian_of_profileHermitian hv i
  have hC (i j : Fin 3) :
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) (-ξ)
        = star ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => v η i)) ξ :=
    coordHermitian_convolution_mul (fun η => u η j) (fun η => v η i) (hc j) (hd i) ξ
  ext i
  have hq (j : Fin 3) : star ((ξ j : ℂ)) = (ξ j : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hterm (j : Fin 3) : ((-ξ) j : ℂ) *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) (-ξ)
      = star (-((ξ j : ℂ) *
        ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ)) := by
    rw [PiLp.neg_apply, Complex.ofReal_neg, hC i j, neg_mul, star_neg, star_mul', hq j,
      Pi.star_apply]
  exact calc rawNavierConvection u v (-ξ) i
      = ∑ j : Fin 3, ((-ξ) j : ℂ) *
          ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) (-ξ) := rfl
    _ = ∑ j : Fin 3, star (-((ξ j : ℂ) *
          ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ)) :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = star (∑ j : Fin 3, -((ξ j : ℂ) *
          ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ)) :=
        (star_sum Finset.univ _).symm
    _ = -(complexConjugate (rawNavierConvection u v ξ)) i := by
        rw [complexConjugate_apply, rawNavierConvection,
          Finset.sum_neg_distrib, star_neg]

/-- The `Complex.I` phase turns the anti-Hermitian sign of the raw convection
back into a conjugation. -/
theorem smul_neg_complexConjugate (z : ComplexSpace) :
    Complex.I • (-complexConjugate z) = complexConjugate (Complex.I • z) := by
  ext i
  show Complex.I * (-star (z i)) = star (Complex.I * z i)
  rw [star_mul', Complex.star_def, Complex.conj_I, neg_mul, mul_neg]

/-- The Leray-dressed continuous Fourier bilinear symbol is Hermitian: the
multiplier is even in the frequency (`complexLeray_neg_frequency`) and
commutes with conjugation (`complexLeray_conjugate`). -/
theorem continuousNavierBilinear_neg (u v : ES → ComplexSpace) (hu : ProfileHermitian u)
    (hv : ProfileHermitian v) : ProfileHermitian (continuousNavierBilinear u v) := by
  intro ξ
  have hraw := rawNavierConvection_neg u v hu hv ξ
  have hinner : Complex.I • (-complexConjugate (rawNavierConvection u v ξ))
      = complexConjugate (Complex.I • rawNavierConvection u v ξ) :=
    smul_neg_complexConjugate (rawNavierConvection u v ξ)
  show complexLeray (spaceProj (-ξ)) (Complex.I • rawNavierConvection u v (-ξ))
      = complexConjugate (complexLeray (spaceProj ξ) (Complex.I • rawNavierConvection u v ξ))
  rw [ContinuousLinearMap.map_neg, hraw, complexLeray_neg_frequency, hinner,
    complexLeray_conjugate]

/-- The time-dependent source is Hermitian for Hermitian trajectories. -/
theorem profileHermitian_continuousNavierSource (u v : ℝ → ES → ComplexSpace)
    (hu : ∀ t, ProfileHermitian (u t)) (hv : ∀ t, ProfileHermitian (v t)) (t : ℝ) :
    ProfileHermitian (continuousNavierSource u v t) :=
  continuousNavierBilinear_neg (u t) (v t) (hu t) (hv t)

/-- The continuous Duhamel term preserves Hermitian symmetry: conjugation
commutes with the Bochner time integral by the unconditional `integral_conj`,
and the heat-damped source is conjugate-symmetric pointwise in time. -/
theorem continuousDuhamel_neg (u v : ℝ → ES → ComplexSpace) (ν : ℝ)
    (hu : ∀ t, ProfileHermitian (u t)) (hv : ∀ t, ProfileHermitian (v t)) (t : ℝ) :
    ProfileHermitian (continuousDuhamel ν u v t) := by
  intro ξ
  ext i
  have key (s : ℝ) :
      heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) (-ξ)
        = star (heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ) :=
    coordHermitian_heatMode (fun ζ => continuousNavierSource u v s ζ i)
      (coordHermitian_of_profileHermitian
        (profileHermitian_continuousNavierSource u v hu hv s) i) ν (t - s) ξ
  show (∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) (-ξ))
      = star (∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ)
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (ae_of_all (volume.restrict (Icc (0 : ℝ) t)) fun s => ?_)
  exact key s

/-- The full mild image preserves Hermitian symmetry. -/
theorem continuousMildImage_neg (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u : ℝ → ES → ComplexSpace) (ha : ProfileHermitian a)
    (hu : ∀ t, ProfileHermitian (u t)) (t : ℝ) :
    ProfileHermitian (continuousMildImage ν hν a u t) := by
  intro ξ
  have h1 := profileHermitian_heatVec a ha ν t ξ
  have h2 := continuousDuhamel_neg u u ν hu hu t ξ
  show heatVec ν t a (-ξ) + continuousDuhamel ν u u t (-ξ)
      = complexConjugate (heatVec ν t a ξ + continuousDuhamel ν u u t ξ)
  rw [h1, h2, complexConjugate_add]

/-! ## Frequency transversality (the Fourier image of incompressibility) -/

/-- The coordinatewise heat flow transports frequency transversality: the
multiplier is a single scalar shared by all three coordinates. -/
theorem profileDivergenceFree_heatVec (a : ES → ComplexSpace)
    (ha : ProfileDivergenceFree a) (ν t : ℝ) : ProfileDivergenceFree (heatVec ν t a) := by
  intro ξ
  have hc : ∀ i : Fin 3, heatVec ν t a ξ i
      = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i := by
    intro i
    show heatMode ν t (fun ζ => a ζ i) ξ = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i
    rw [heatMode]
  calc ∑ i : Fin 3, (spaceProj ξ i : ℂ) * heatVec ν t a ξ i
      = ∑ i : Fin 3, (spaceProj ξ i : ℂ)
          * (((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i) :=
        Finset.sum_congr rfl fun i _ => by rw [hc i]
    _ = ∑ i : Fin 3, ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)
          * ((spaceProj ξ i : ℂ) * a ξ i) :=
        Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    _ = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)
        * ∑ i : Fin 3, (spaceProj ξ i : ℂ) * a ξ i := by rw [← Finset.mul_sum]
    _ = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * 0 := by rw [ha ξ]
    _ = 0 := mul_zero _

/-- **Frequency transversality of the Duhamel term.**  Pointwise in time the
source is a Leray-projected vector, so its output dot product vanishes by
`complexLeray_transverse`; under the stated coordinate integrability the dot
product of the coordinate Bochner integrals equals the integral of the
pointwise dot product (`ContinuousLinearMap.integral_comp_comm` scalarwise plus
`integral_finsetSum`), so the time integral is `0` too. -/
theorem profileDivergenceFree_continuousDuhamel (u v : ℝ → ES → ComplexSpace) (ν t : ℝ)
    (hKint : ∀ ξ : ES, ∀ i : Fin 3, Integrable
      (fun s : ℝ => heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ)
      (volume.restrict (Icc (0 : ℝ) t))) :
    ProfileDivergenceFree (continuousDuhamel ν u v t) := by
  intro ξ
  have hleg (i : Fin 3) : (spaceProj ξ i : ℂ) *
      (∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ)
      = ∫ s in Icc (0 : ℝ) t,
          (spaceProj ξ i : ℂ) *
            heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ :=
    (ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.mul ℂ ℂ (spaceProj ξ i : ℂ)) (hKint ξ i)).symm
  have hzero (s : ℝ) : ∑ i : Fin 3, (spaceProj ξ i : ℂ) *
      heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ = 0 := by
    simp only [heatMode, continuousNavierSource, continuousNavierBilinear, continuousLeray]
    set c : ℂ := ((Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)) : ℝ) : ℂ)) with hc
    set W := Complex.I • rawNavierConvection (u s) (v s) ξ with hW
    have h1 : (∑ i : Fin 3, (spaceProj ξ i : ℂ) * (c * complexLeray (spaceProj ξ) W i))
        = ∑ i : Fin 3, c * ((spaceProj ξ i : ℂ) * complexLeray (spaceProj ξ) W i) :=
      Finset.sum_congr rfl fun i _ => mul_left_comm _ c _
    rw [h1, ← Finset.mul_sum, complexLeray_transverse, mul_zero]
  calc ∑ i : Fin 3, (spaceProj ξ i : ℂ)
      * (∫ s in Icc (0 : ℝ) t,
          heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ)
      = ∑ i : Fin 3, ∫ s in Icc (0 : ℝ) t,
          (spaceProj ξ i : ℂ) *
            heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ :=
        Finset.sum_congr rfl fun i _ => hleg i
    _ = ∫ s in Icc (0 : ℝ) t, ∑ i : Fin 3, (spaceProj ξ i : ℂ) *
          heatMode ν (t - s) (fun ζ => continuousNavierSource u v s ζ i) ξ :=
        (integral_finsetSum Finset.univ (fun i _ =>
          (hKint ξ i).const_mul (spaceProj ξ i : ℂ))).symm
    _ = ∫ s in Icc (0 : ℝ) t, 0 :=
        integral_congr_ae (ae_of_all (volume.restrict (Icc (0 : ℝ) t)) fun s => hzero s)
    _ = 0 := integral_zero _ _

/-- Frequency transversality is preserved by the mild map. -/
theorem profileDivergenceFree_continuousMildImage (ν : ℝ) (hν : 0 < ν)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace)
    (ha : ProfileDivergenceFree a) (t : ℝ)
    (hKint : ∀ ξ : ES, ∀ i : Fin 3, Integrable
      (fun s : ℝ => heatMode ν (t - s) (fun ζ => continuousNavierSource u u s ζ i) ξ)
      (volume.restrict (Icc (0 : ℝ) t))) :
    ProfileDivergenceFree (continuousMildImage ν hν a u t) := by
  intro ξ
  have hV := profileDivergenceFree_heatVec a ha ν t ξ
  have hD := profileDivergenceFree_continuousDuhamel u u ν t hKint ξ
  show ∑ i : Fin 3, (spaceProj ξ i : ℂ)
      * (heatVec ν t a ξ i + continuousDuhamel ν u u t ξ i) = 0
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hV, hD, add_zero]

end Navier.Analysis.ContinuousLeiLinReality

#print axioms Navier.Analysis.ContinuousLeiLinReality.complexConjugate_apply
#print axioms Navier.Analysis.ContinuousLeiLinReality.complexConjugate_add
#print axioms Navier.Analysis.ContinuousLeiLinReality.coordHermitian_of_profileHermitian
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileHermitian_of_coordHermitian
#print axioms Navier.Analysis.ContinuousLeiLinReality.coordHermitian_heatMode
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileHermitian_heatVec
#print axioms Navier.Analysis.ContinuousLeiLinReality.coordHermitian_convolution_mul
#print axioms Navier.Analysis.ContinuousLeiLinReality.rawNavierConvection_neg
#print axioms Navier.Analysis.ContinuousLeiLinReality.smul_neg_complexConjugate
#print axioms Navier.Analysis.ContinuousLeiLinReality.continuousNavierBilinear_neg
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileHermitian_continuousNavierSource
#print axioms Navier.Analysis.ContinuousLeiLinReality.continuousDuhamel_neg
#print axioms Navier.Analysis.ContinuousLeiLinReality.continuousMildImage_neg
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileDivergenceFree_heatVec
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileDivergenceFree_continuousDuhamel
#print axioms Navier.Analysis.ContinuousLeiLinReality.profileDivergenceFree_continuousMildImage
