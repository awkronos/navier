import Navier.Analysis.PeriodicDatumFourierBridge
import Navier.Analysis.PeriodicEnergyCriticalObstruction
import Navier.Analysis.PeriodicFourierReconstruction
import Navier.Construction.TemporalMeanUpdate

/-!
# Reality and divergence constraints for periodic datum coefficients

This module continues the native bridge without replacing the datum by a
projected surrogate.  It proves Hermitian symmetry and Fourier transversality
for the actual unit-cube coefficients and stores those coefficients in the
completed weighted lattice carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators ContDiff ComplexConjugate ENNReal

namespace Navier.Analysis.PeriodicDatumFourierConstraints

open Set MeasureTheory
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.PeriodicDatumFourierBridge
open Navier.Analysis.PeriodicEnergyCriticalObstruction
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Construction

/-- Complex conjugation reverses the index of the exact unit-interval Fourier
coefficient. -/
theorem conj_unitCoeff (f : ℝ → ℂ) (n : ℤ) :
    star (SmoothFourierData.unitCoeff f n) =
      SmoothFourierData.unitCoeff (fun x => star (f x)) (-n) := by
  rw [SmoothFourierData.unitCoeff_eq_integral,
    SmoothFourierData.unitCoeff_eq_integral]
  change conj (∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) * f x) = _
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [map_mul, neg_neg, fourier_neg, starRingEnd_apply]
  rw [star_star]

/-- Fourier coefficient of a derivative on a unit-periodic line.  This form,
including the zero mode, is the multiplier identity used for divergence. -/
theorem unitCoeff_derivative {f f' : ℝ → ℂ} (n : ℤ)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (hp : f 1 = f 0) :
    SmoothFourierData.unitCoeff f' n =
      (TorusInverse.omega * (n : ℂ)) * SmoothFourierData.unitCoeff f n := by
  by_cases hn : n = 0
  · subst n
    have hderiv : deriv f = f' := funext fun x => (hd x).deriv
    rw [SmoothFourierData.unitCoeff_eq_integral]
    simp only [neg_zero, fourier_zero, one_mul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_deriv_eq_sub' f hderiv
      (fun x _ => (hd x).differentiableAt) hc.continuousOn, hp, sub_self]
  · have hfreq : TorusInverse.omega * (n : ℂ) ≠ 0 := by
      exact mul_ne_zero TorusInverse.omega_ne_zero (by exact_mod_cast hn)
    have hibp := SmoothFourierData.unitCoeff_of_hasDerivAt hn hd hc hp
    rw [hibp, ← mul_assoc, mul_inv_cancel₀ hfreq, one_mul]

/-- The reassociation map as an actual continuous linear map, used to identify
coordinate derivatives of the lifted datum with official Frechet derivatives. -/
def pointToSpaceCLM : ParametricTorusInverse.Point →L[ℝ] Space :=
  ContinuousLinearMap.pi ![
    ContinuousLinearMap.fst ℝ ℝ TorusInverse.Plane,
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ TorusInverse.Plane),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ TorusInverse.Plane)]

@[simp] theorem pointToSpaceCLM_apply (q : ParametricTorusInverse.Point) :
    pointToSpaceCLM q = pointToSpace q := by
  ext i
  fin_cases i <;> rfl

/-- Exact chain rule for a scalar coordinate of the native datum lift. -/
theorem nativeScalarSource_fderiv {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (i : Fin 3)
    (q v : ParametricTorusInverse.Point) :
    fderiv ℝ (nativeScalarSource u₀ i) q v =
      (fderiv ℝ u₀ (pointToSpace q) (pointToSpaceCLM v) i : ℂ) := by
  change fderiv ℝ
      (Complex.ofRealCLM ∘ (ContinuousLinearMap.proj (R := ℝ) i) ∘
        u₀ ∘ pointToSpace) q v = _
  have hu := (hu₀.differentiable (by simp) (pointToSpace q)).hasFDerivAt
  have hspace : HasFDerivAt pointToSpace pointToSpaceCLM q := by
    convert pointToSpaceCLM.hasFDerivAt using 1
    funext w
    exact (pointToSpaceCLM_apply w).symm
  have hcomp := hu.comp q hspace
  have hcoord := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp q hcomp
  have hreal := Complex.ofRealCLM.hasFDerivAt.comp q hcoord
  have heq := congrArg
    (fun L : ParametricTorusInverse.Point →L[ℝ] ℂ => L v) hreal.fderiv
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
    pointToSpaceCLM_apply] using heq

/-- The exact multiplier identity for the first coordinate of a plane
coefficient. -/
theorem planeCoefficient_partialX {f : TorusInverse.Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFourierData.UnitPeriodic f)
    (k : TorusInverse.Frequency) :
    SmoothFourierData.coefficient (SmoothFourierData.partialX f) k =
      (TorusInverse.omega * (k.1 : ℂ)) *
        SmoothFourierData.coefficient f k := by
  have hinner : (fun y => SmoothFourierData.unitCoeff
        (fun x => SmoothFourierData.partialX f (x, y)) k.1) =
      (fun y => (TorusInverse.omega * (k.1 : ℂ)) *
        SmoothFourierData.unitCoeff (fun x => f (x, y)) k.1) := by
    funext y
    apply unitCoeff_derivative
    · intro x
      exact SmoothFourierData.hasDerivAt_slice
        ((hf.differentiable (by simp)) (x, y))
    · exact (SmoothFourierData.partialX_smooth hf).continuous.comp
        (continuous_id.prodMk continuous_const)
    · simpa using hp (0, y) (1, 0)
  unfold SmoothFourierData.coefficient
  rw [hinner, SmoothFourierData.unitCoeff_const_mul]

/-- The second plane-coordinate derivative. -/
def planePartialY (f : TorusInverse.Plane → ℂ) (Y : TorusInverse.Plane) : ℂ :=
  fderiv ℝ f Y (0, 1)

theorem planePartialY_smooth {f : TorusInverse.Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (planePartialY f) :=
  (ContinuousLinearMap.apply ℝ ℂ (0, 1)).contDiff.comp
    (hf.fderiv_right (by simp))

def swapPlaneCLM : TorusInverse.Plane →L[ℝ] TorusInverse.Plane :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem swapPlaneCLM_apply (Y : TorusInverse.Plane) :
    swapPlaneCLM Y = (Y.2, Y.1) := rfl

theorem swap_partialX_swap {f : TorusInverse.Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    SmoothFourierData.swapFunction
        (SmoothFourierData.partialX (SmoothFourierData.swapFunction f)) =
      planePartialY f := by
  funext Y
  have hswap : HasFDerivAt (fun Z : TorusInverse.Plane => (Z.2, Z.1))
      swapPlaneCLM (Y.2, Y.1) := by
    convert swapPlaneCLM.hasFDerivAt using 1
    funext Z
    exact (swapPlaneCLM_apply Z).symm
  have hf' := (hf.differentiable (by simp) Y).hasFDerivAt.comp (Y.2, Y.1) hswap
  have heq := congrArg (fun L : TorusInverse.Plane →L[ℝ] ℂ => L (1, 0)) hf'.fderiv
  change fderiv ℝ (f ∘ fun Z : TorusInverse.Plane => (Z.2, Z.1))
      (Y.2, Y.1) (1, 0) = fderiv ℝ f Y (0, 1)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    swapPlaneCLM_apply] using heq

/-- The exact multiplier identity for the second coordinate of a plane
coefficient. -/
theorem planeCoefficient_partialY {f : TorusInverse.Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFourierData.UnitPeriodic f)
    (k : TorusInverse.Frequency) :
    SmoothFourierData.coefficient (planePartialY f) k =
      (TorusInverse.omega * (k.2 : ℂ)) *
        SmoothFourierData.coefficient f k := by
  have hswap : SmoothFourierData.swapFunction (planePartialY f) =
      SmoothFourierData.partialX (SmoothFourierData.swapFunction f) := by
    rw [← swap_partialX_swap hf]
    rfl
  rw [SmoothFourierData.coefficient_swap (planePartialY_smooth hf).continuous k,
    hswap,
    planeCoefficient_partialX (SmoothFourierData.swapFunction_smooth hf)
      (SmoothFourierData.swapFunction_periodic hp) (k.2, k.1),
    ← SmoothFourierData.coefficient_swap hf.continuous k]

/-- The third source-coordinate derivative. -/
def torusYPartial (f : ScalarSource) (q : ParametricTorusInverse.Point) : ℂ :=
  fderiv ℝ f q (0, (0, 1))

theorem torusYPartial_smooth {f : ScalarSource} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (torusYPartial f) :=
  ParametricTorusInverse.fixedPartial_smooth hf (0, (0, 1))

theorem slice_torusYPartial {f : ScalarSource} (hf : ContDiff ℝ ∞ f)
    (z : ℝ) :
    ParametricTorusInverse.slice (torusYPartial f) z =
      planePartialY (ParametricTorusInverse.slice f z) := by
  funext Y
  change fderiv ℝ f (z, Y) (0, (0, 1)) =
    fderiv ℝ (ParametricTorusInverse.slice f z) Y (0, 1)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    using (congrArg (fun L : TorusInverse.Plane →L[ℝ] ℂ => L (0, 1))
      (ParametricTorusInverse.slice_hasFDerivAt hf z Y).fderiv).symm

/-- The first-coordinate multiplier identity for the full cube coefficient. -/
theorem scalarCoefficient_parameterPartial {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (k : LatticeMode) :
    scalarCoefficient (ParametricTorusInverse.parameterPartial f) k =
      (TorusInverse.omega * (k.1 : ℂ)) * scalarCoefficient f k := by
  unfold scalarCoefficient
  apply unitCoeff_derivative
  · exact fun z => ParametricTorusInverse.coefficient_hasDerivAt hf k.2 z
  · exact (ParametricTorusInverse.coefficient_smooth
      (ParametricTorusInverse.parameterPartial_smooth hf) k.2).continuous
  · have hper := congrArg
      (fun g : TorusInverse.Plane → ℂ => SmoothFourierData.coefficient g k.2)
      (funext fun Y => hp.2 0 Y)
    change SmoothFourierData.coefficient (fun Y => f (1, Y)) k.2 =
      SmoothFourierData.coefficient
        (fun Y => f (0, Y)) k.2
    simpa only [zero_add] using hper

/-- The second-coordinate multiplier identity for the full cube coefficient. -/
theorem scalarCoefficient_torusXPartial {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (k : LatticeMode) :
    scalarCoefficient (ParametricTorusInverse.torusXPartial f) k =
      (TorusInverse.omega * (k.2.1 : ℂ)) * scalarCoefficient f k := by
  unfold scalarCoefficient
  have heq : (fun z => ParametricTorusInverse.coefficient
        (ParametricTorusInverse.torusXPartial f) z k.2) =
      (fun z => (TorusInverse.omega * (k.2.1 : ℂ)) *
        ParametricTorusInverse.coefficient f z k.2) := by
    funext z
    unfold ParametricTorusInverse.coefficient
    rw [ParametricTorusInverse.slice_torusXPartial hf z,
      planeCoefficient_partialX (ParametricTorusInverse.slice_smooth hf z) (hp.1 z)]
  rw [heq, SmoothFourierData.unitCoeff_const_mul]

/-- The third-coordinate multiplier identity for the full cube coefficient. -/
theorem scalarCoefficient_torusYPartial {f : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic3 f) (k : LatticeMode) :
    scalarCoefficient (torusYPartial f) k =
      (TorusInverse.omega * (k.2.2 : ℂ)) * scalarCoefficient f k := by
  unfold scalarCoefficient
  have heq : (fun z => ParametricTorusInverse.coefficient
        (torusYPartial f) z k.2) =
      (fun z => (TorusInverse.omega * (k.2.2 : ℂ)) *
        ParametricTorusInverse.coefficient f z k.2) := by
    funext z
    unfold ParametricTorusInverse.coefficient
    rw [slice_torusYPartial hf z,
      planeCoefficient_partialY (ParametricTorusInverse.slice_smooth hf z) (hp.1 z)]
  rw [heq, SmoothFourierData.unitCoeff_const_mul]

@[simp] theorem pointToSpaceCLM_parameterDirection :
    pointToSpaceCLM (1, 0) = basisVector 0 := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem pointToSpaceCLM_firstTorusDirection :
    pointToSpaceCLM (0, (1, 0)) = basisVector 1 := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem pointToSpaceCLM_secondTorusDirection :
    pointToSpaceCLM (0, (0, 1)) = basisVector 2 := by
  ext i
  fin_cases i <;> rfl

theorem parameterPartial_nativeScalarSource {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (i : Fin 3) (q : ParametricTorusInverse.Point) :
    ParametricTorusInverse.parameterPartial (nativeScalarSource u₀ i) q =
      (fderiv ℝ u₀ (pointToSpace q) (basisVector 0) i : ℂ) := by
  unfold ParametricTorusInverse.parameterPartial
  rw [nativeScalarSource_fderiv hu₀, pointToSpaceCLM_parameterDirection]

theorem torusXPartial_nativeScalarSource {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (i : Fin 3) (q : ParametricTorusInverse.Point) :
    ParametricTorusInverse.torusXPartial (nativeScalarSource u₀ i) q =
      (fderiv ℝ u₀ (pointToSpace q) (basisVector 1) i : ℂ) := by
  unfold ParametricTorusInverse.torusXPartial
  rw [nativeScalarSource_fderiv hu₀, pointToSpaceCLM_firstTorusDirection]

theorem torusYPartial_nativeScalarSource {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (i : Fin 3) (q : ParametricTorusInverse.Point) :
    torusYPartial (nativeScalarSource u₀ i) q =
      (fderiv ℝ u₀ (pointToSpace q) (basisVector 2) i : ℂ) := by
  unfold torusYPartial
  rw [nativeScalarSource_fderiv hu₀, pointToSpaceCLM_secondTorusDirection]

/-- Linearity of the exact unit-interval coefficient on continuous inputs. -/
theorem unitCoeff_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) :
    SmoothFourierData.unitCoeff (fun x => f x + g x) n =
      SmoothFourierData.unitCoeff f n + SmoothFourierData.unitCoeff g n := by
  simp_rw [SmoothFourierData.unitCoeff_eq_integral, mul_add]
  exact intervalIntegral.integral_add
    ((((fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1)).mul hf).intervalIntegrable 0 1)
    ((((fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1)).mul hg).intervalIntegrable 0 1)

/-- Linearity of the exact cube coefficient on smooth inputs. -/
theorem scalarCoefficient_add {f g : ScalarSource}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : LatticeMode) :
    scalarCoefficient (fun q => f q + g q) k =
      scalarCoefficient f k + scalarCoefficient g k := by
  unfold scalarCoefficient
  have heq : (fun z => ParametricTorusInverse.coefficient
        (fun q => f q + g q) z k.2) =
      (fun z => ParametricTorusInverse.coefficient f z k.2 +
        ParametricTorusInverse.coefficient g z k.2) := by
    funext z
    unfold ParametricTorusInverse.coefficient ParametricTorusInverse.slice
    exact Navier.Construction.TemporalMeanUpdate.coefficient_add
      (ParametricTorusInverse.slice_smooth hf z)
      (ParametricTorusInverse.slice_smooth hg z) k.2
  rw [heq]
  exact unitCoeff_add
    (ParametricTorusInverse.coefficient_smooth hf k.2).continuous
    (ParametricTorusInverse.coefficient_smooth hg k.2).continuous k.1

@[simp] theorem scalarCoefficient_zero (k : LatticeMode) :
    scalarCoefficient (0 : ScalarSource) k = 0 := by
  rw [scalarCoefficient_eq_tripleIntegral]
  simp

/-- The lifted complex divergence, written in the three derivative operators
whose Fourier multipliers were proved above. -/
def nativeDivergenceSource (u₀ : VelocityField) : ScalarSource := fun q =>
  ParametricTorusInverse.parameterPartial (nativeScalarSource u₀ 0) q +
    ParametricTorusInverse.torusXPartial (nativeScalarSource u₀ 1) q +
      torusYPartial (nativeScalarSource u₀ 2) q

theorem nativeDivergenceSource_eq {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) (q : ParametricTorusInverse.Point) :
    nativeDivergenceSource u₀ q =
      (staticDivergence u₀ (pointToSpace q) : ℂ) := by
  rw [nativeDivergenceSource, parameterPartial_nativeScalarSource hu₀,
    torusXPartial_nativeScalarSource hu₀, torusYPartial_nativeScalarSource hu₀]
  simp only [staticDivergence, Fin.sum_univ_three, Complex.ofReal_add]

theorem nativeDivergenceSource_smooth {u₀ : VelocityField}
    (hu₀ : ContDiff ℝ ∞ u₀) : ContDiff ℝ ∞ (nativeDivergenceSource u₀) :=
  ((ParametricTorusInverse.parameterPartial_smooth (nativeScalarSource_smooth hu₀ 0)).add
    (ParametricTorusInverse.torusXPartial_smooth (nativeScalarSource_smooth hu₀ 1))).add
      (torusYPartial_smooth (nativeScalarSource_smooth hu₀ 2))

/-- Pointwise official divergence-free data have transverse actual Fourier
coefficients.  No Leray projection is inserted. -/
theorem nativeCoefficient_divergenceFree {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (k : LatticeMode) :
    inner ℂ (complexFrequency (latticeFrequency k))
      (complexEuclideanPoint (nativeCoefficient u₀ k)) = 0 := by
  have hsource : nativeDivergenceSource u₀ = 0 := by
    funext q
    rw [nativeDivergenceSource_eq hu₀.1 q, hu₀.2.1 (pointToSpace q)]
    rfl
  have hcoeff : scalarCoefficient (nativeDivergenceSource u₀) k = 0 := by
    rw [hsource, scalarCoefficient_zero]
  unfold nativeDivergenceSource at hcoeff
  rw [scalarCoefficient_add
      ((ParametricTorusInverse.parameterPartial_smooth (nativeScalarSource_smooth hu₀.1 0)).add
        (ParametricTorusInverse.torusXPartial_smooth (nativeScalarSource_smooth hu₀.1 1)))
      (torusYPartial_smooth (nativeScalarSource_smooth hu₀.1 2)) k,
    scalarCoefficient_add
      (ParametricTorusInverse.parameterPartial_smooth (nativeScalarSource_smooth hu₀.1 0))
      (ParametricTorusInverse.torusXPartial_smooth (nativeScalarSource_smooth hu₀.1 1)) k,
    scalarCoefficient_parameterPartial (nativeScalarSource_smooth hu₀.1 0)
      (nativeScalarSource_periodic hu₀.2.2 0) k,
    scalarCoefficient_torusXPartial (nativeScalarSource_smooth hu₀.1 1)
      (nativeScalarSource_periodic hu₀.2.2 1) k,
    scalarCoefficient_torusYPartial (nativeScalarSource_smooth hu₀.1 2)
      (nativeScalarSource_periodic hu₀.2.2 2) k] at hcoeff
  have hsum : (k.1 : ℂ) * nativeCoefficient u₀ k 0 +
      (k.2.1 : ℂ) * nativeCoefficient u₀ k 1 +
        (k.2.2 : ℂ) * nativeCoefficient u₀ k 2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left TorusInverse.omega_ne_zero
    calc
      TorusInverse.omega *
          ((k.1 : ℂ) * nativeCoefficient u₀ k 0 +
            (k.2.1 : ℂ) * nativeCoefficient u₀ k 1 +
              (k.2.2 : ℂ) * nativeCoefficient u₀ k 2) =
        (TorusInverse.omega * (k.1 : ℂ)) * nativeCoefficient u₀ k 0 +
          (TorusInverse.omega * (k.2.1 : ℂ)) * nativeCoefficient u₀ k 1 +
            (TorusInverse.omega * (k.2.2 : ℂ)) * nativeCoefficient u₀ k 2 := by ring
      _ = 0 := by simpa only [nativeCoefficient_apply] using hcoeff
  rw [inner_complexFrequency]
  simpa [latticeFrequency, Fin.sum_univ_three] using hsum

/-- Complex conjugation reverses both indices of the exact square
coefficient. -/
theorem conj_planeCoefficient (f : TorusInverse.Plane → ℂ)
    (k : TorusInverse.Frequency) :
    star (SmoothFourierData.coefficient f k) =
      SmoothFourierData.coefficient (fun Y => star (f Y)) (-k) := by
  unfold SmoothFourierData.coefficient
  rw [conj_unitCoeff]
  apply congrArg (fun g : ℝ → ℂ => SmoothFourierData.unitCoeff g (-k.2))
  funext y
  rw [conj_unitCoeff]
  rfl

/-- Complex conjugation reverses all three indices of the exact cube
coefficient. -/
theorem conj_scalarCoefficient (f : ScalarSource) (k : LatticeMode) :
    star (scalarCoefficient f k) =
      scalarCoefficient (fun q => star (f q)) (-k) := by
  unfold scalarCoefficient ParametricTorusInverse.coefficient
  rw [conj_unitCoeff]
  apply congrArg (fun g : ℝ → ℂ => SmoothFourierData.unitCoeff g (-k.1))
  funext z
  rw [conj_planeCoefficient]
  rfl

/-- The scalar source lifted from a real official datum is fixed by complex
conjugation. -/
@[simp] theorem star_nativeScalarSource (u₀ : VelocityField) (i : Fin 3)
    (q : ParametricTorusInverse.Point) :
    star (nativeScalarSource u₀ i q) = nativeScalarSource u₀ i q := by
  simp [nativeScalarSource]

/-- The actual native coefficient sequence has the Hermitian symmetry needed
to reconstruct a real velocity field. -/
theorem nativeCoefficient_neg (u₀ : VelocityField) (k : LatticeMode)
    (i : Fin 3) :
    nativeCoefficient u₀ (-k) i = star (nativeCoefficient u₀ k i) := by
  rw [nativeCoefficient_apply, nativeCoefficient_apply]
  symm
  rw [conj_scalarCoefficient]
  apply congrArg (fun f : ScalarSource => scalarCoefficient f (-k))
  funext q
  exact star_nativeScalarSource u₀ i q

/-- The componentwise symmetry theorem inhabits the reconstruction module's
exact vector-valued Hermitian premise. -/
theorem nativeCoefficient_hermitian (u₀ : VelocityField) :
    NativeCoefficientHermitian u₀ := by
  intro k
  ext i
  exact nativeCoefficient_neg u₀ k i

/-- The exact native initial carrier is in the divergence-free subspace used
by the critical mild evolution. -/
theorem nativeInitialCarrier_divergenceFree
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    LatticeDivergenceFree (nativeInitialCarrier u₀ hu₀) := by
  intro k
  rw [nativeInitialCarrier_coefficient]
  exact nativeCoefficient_divergenceFree hu₀ k

/-- The completed native carrier retains the exact real-field symmetry. -/
theorem nativeInitialCarrier_hermitianReal
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    LatticeHermitianReal (nativeInitialCarrier u₀ hu₀) := by
  intro k i
  rw [nativeInitialCarrier_coefficient, nativeInitialCarrier_coefficient]
  exact nativeCoefficient_neg u₀ k i

end Navier.Analysis.PeriodicDatumFourierConstraints
