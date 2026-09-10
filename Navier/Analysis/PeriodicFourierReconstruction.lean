import Navier.Analysis.PeriodicDatumFourierBridge
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Physical reconstruction of the periodic critical lattice carrier

This module decodes the completed weighted lattice carrier into the literal
unit-periodic Fourier series on `ℝ³`.  Absolute convergence follows from the
existing weighted `ℓ¹` norm, continuity follows by the Weierstrass test, and
Hermitian symmetry makes the complex reconstruction exactly real.  The final
definitions consume `PeriodicDatumFourierBridge.nativeCoefficient`, so the
official smooth periodic datum initializes the same carrier used by the mild
dynamics.

This is a reconstruction layer, not a proof of periodic global regularity:
classical spacetime smoothness, pressure recovery, the PDE identity, and a
global arbitrary-data estimate remain downstream obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal
open Set Filter Topology

namespace Navier.Analysis.PeriodicFourierReconstruction

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.PeriodicDatumFourierBridge

/-- Reassociate the nested lattice mode with Mathlib's native three-torus
index. -/
def latticeTorusIndex (m : LatticeMode) : Fin 3 → ℤ :=
  ![m.1, m.2.1, m.2.2]

/-- Project a physical point to the native unit three-torus. -/
def unitTorusPoint (x : Space) : UnitAddTorus (Fin 3) :=
  fun i => (x i : UnitAddCircle)

/-- The positive Fourier character `exp(2π i k · x)`, expressed through
Mathlib's native product-torus character. -/
def latticeCharacter (m : LatticeMode) (x : Space) : ℂ :=
  UnitAddTorus.mFourier (latticeTorusIndex m) (unitTorusPoint x)

theorem continuous_latticeCharacter (m : LatticeMode) :
    Continuous (latticeCharacter m) := by
  unfold latticeCharacter unitTorusPoint
  fun_prop

theorem latticeTorusIndex_neg (m : LatticeMode) :
    latticeTorusIndex (-m) = -latticeTorusIndex m := by
  ext i
  fin_cases i <;> simp [latticeTorusIndex]

theorem star_latticeCharacter (m : LatticeMode) (x : Space) :
    star (latticeCharacter m x) = latticeCharacter (-m) x := by
  unfold latticeCharacter
  rw [latticeTorusIndex_neg]
  simpa using (UnitAddTorus.mFourier_neg
    (n := latticeTorusIndex m) (x := unitTorusPoint x)).symm

theorem norm_latticeCharacter (m : LatticeMode) (x : Space) :
    ‖latticeCharacter m x‖ = 1 := by
  simp [latticeCharacter, UnitAddTorus.mFourier]

theorem unitTorusPoint_add_basisVector (x : Space) (i : Fin 3) :
    unitTorusPoint (x + basisVector i) = unitTorusPoint x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [unitTorusPoint, basisVector]
  · simp [unitTorusPoint, basisVector, hji]

theorem latticeCharacter_add_basisVector (m : LatticeMode)
    (x : Space) (i : Fin 3) :
    latticeCharacter m (x + basisVector i) = latticeCharacter m x := by
  unfold latticeCharacter
  rw [unitTorusPoint_add_basisVector]

/-- The literal Fourier summand obtained from the existing coefficient
decoder. -/
def latticeFourierTerm (u : WeightedLatticeBanach)
    (m : LatticeMode) (x : Space) : ComplexE3 :=
  latticeCharacter m x •
    complexEuclideanPoint (weightedLatticeCoefficient u m)

theorem norm_latticeFourierTerm (u : WeightedLatticeBanach)
    (m : LatticeMode) (x : Space) :
    ‖latticeFourierTerm u m x‖ =
      complexEuclideanNorm (weightedLatticeCoefficient u m) := by
  unfold latticeFourierTerm complexEuclideanNorm
  rw [norm_smul, norm_latticeCharacter, one_mul]

/-- Dropping the inhomogeneous weight preserves summability. -/
theorem summable_decodedCoefficientNorm (u : WeightedLatticeBanach) :
    Summable fun m : LatticeMode =>
      complexEuclideanNorm (weightedLatticeCoefficient u m) := by
  exact (latticeWeightedL1_coefficient u).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun m => le_mul_of_one_le_left (norm_nonneg _)
      (one_le_latticeModeWeight m))

theorem summable_latticeFourierTerm (u : WeightedLatticeBanach) (x : Space) :
    Summable fun m : LatticeMode => latticeFourierTerm u m x := by
  apply Summable.of_norm
  simpa only [norm_latticeFourierTerm] using summable_decodedCoefficientNorm u

/-- The actual absolutely convergent complex Fourier reconstruction. -/
def complexFourierReconstruction (u : WeightedLatticeBanach) (x : Space) : ComplexE3 :=
  ∑' m : LatticeMode, latticeFourierTerm u m x

/-- The physical Fourier series is uniformly bounded by the completed
weighted-carrier norm. -/
theorem norm_complexFourierReconstruction_le (u : WeightedLatticeBanach) (x : Space) :
    ‖complexFourierReconstruction u x‖ ≤ ‖u‖ := by
  calc
    ‖complexFourierReconstruction u x‖ ≤
        ∑' m : LatticeMode, ‖latticeFourierTerm u m x‖ :=
      norm_tsum_le_tsum_norm (summable_latticeFourierTerm u x).norm
    _ = ∑' m : LatticeMode,
        complexEuclideanNorm (weightedLatticeCoefficient u m) := by
      apply tsum_congr
      exact fun m => norm_latticeFourierTerm u m x
    _ ≤ ∑' m : LatticeMode,
        latticeWeightedAmplitude (weightedLatticeCoefficient u) m := by
      exact (summable_decodedCoefficientNorm u).tsum_le_tsum
        (fun m => le_mul_of_one_le_left (norm_nonneg _)
          (one_le_latticeModeWeight m))
        (latticeWeightedL1_coefficient u)
    _ = ‖u‖ := tsum_latticeWeightedAmplitude_coefficient u

theorem continuous_complexFourierReconstruction (u : WeightedLatticeBanach) :
    Continuous (complexFourierReconstruction u) := by
  apply continuous_tsum
  · intro m
    exact (continuous_latticeCharacter m).smul continuous_const
  · exact summable_decodedCoefficientNorm u
  · intro m x
    exact (norm_latticeFourierTerm u m x).le

theorem complexFourierReconstruction_periodic (u : WeightedLatticeBanach) :
    SpatiallyPeriodic (complexFourierReconstruction u) := by
  intro x i
  apply tsum_congr
  intro m
  unfold latticeFourierTerm
  rw [latticeCharacter_add_basisVector]

/-- Coordinate evaluation on the Hermitian Euclidean carrier. -/
def complexE3CoordinateCLM (i : Fin 3) : ComplexE3 →L[ℂ] ℂ :=
  EuclideanSpace.proj i

/-- Hermitian symmetry of the decoded lattice coefficients. -/
def LatticeHermitian (u : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode,
    weightedLatticeCoefficient u (-m) =
      complexConjugate (weightedLatticeCoefficient u m)

theorem star_latticeFourierTerm_apply {u : WeightedLatticeBanach}
    (hu : LatticeHermitian u) (m : LatticeMode) (x : Space) (i : Fin 3) :
    star (latticeFourierTerm u m x i) = latticeFourierTerm u (-m) x i := by
  change star (latticeCharacter m x * weightedLatticeCoefficient u m i) =
    latticeCharacter (-m) x * weightedLatticeCoefficient u (-m) i
  rw [star_mul, star_latticeCharacter, hu]
  simp [complexConjugate, mul_comm]

/-- Hermitian symmetry makes each coordinate of the completed complex series
fixed by conjugation. -/
theorem star_complexFourierReconstruction_apply {u : WeightedLatticeBanach}
    (hu : LatticeHermitian u) (x : Space) (i : Fin 3) :
    star (complexFourierReconstruction u x i) = complexFourierReconstruction u x i := by
  have hsum := summable_latticeFourierTerm u x
  unfold complexFourierReconstruction
  change star (complexE3CoordinateCLM i (∑' m : LatticeMode,
      latticeFourierTerm u m x)) =
    complexE3CoordinateCLM i (∑' m : LatticeMode, latticeFourierTerm u m x)
  rw [(complexE3CoordinateCLM i).map_tsum hsum, tsum_star]
  calc
    (∑' m : LatticeMode, star (latticeFourierTerm u m x i)) =
        ∑' m : LatticeMode, latticeFourierTerm u (-m) x i :=
      tsum_congr (fun m => star_latticeFourierTerm_apply hu m x i)
    _ = ∑' m : LatticeMode, latticeFourierTerm u m x i :=
      (Equiv.neg LatticeMode).tsum_eq (fun m => latticeFourierTerm u m x i)

/-- The real physical velocity obtained by coordinatewise real-part
extraction from the convergent complex series. -/
def physicalFourierReconstruction (u : WeightedLatticeBanach) : VelocityField :=
  fun x i => (complexFourierReconstruction u x i).re

theorem continuous_physicalFourierReconstruction (u : WeightedLatticeBanach) :
    Continuous (physicalFourierReconstruction u) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_re.comp
    ((complexE3CoordinateCLM i).continuous.comp
      (continuous_complexFourierReconstruction u))

theorem physicalFourierReconstruction_periodic (u : WeightedLatticeBanach) :
    SpatiallyPeriodicDatum (physicalFourierReconstruction u) := by
  intro x i
  have h := complexFourierReconstruction_periodic u x i
  unfold physicalFourierReconstruction
  rw [h]

/-- Under Hermitian symmetry, real-part extraction loses no information: the
complex series is exactly the complexification of the physical velocity. -/
theorem complexOfReal_physicalFourierReconstruction {u : WeightedLatticeBanach}
    (hu : LatticeHermitian u) (x : Space) :
    complexEuclideanPoint (complexOfReal (physicalFourierReconstruction u x)) =
      complexFourierReconstruction u x := by
  ext i
  apply Complex.ext
  · simp [complexOfReal, complexOfParts, physicalFourierReconstruction]
  · have him := congrArg Complex.im (star_complexFourierReconstruction_apply hu x i)
    simp at him
    simp [complexOfReal, complexOfParts]
    linarith

/-- Encode any weighted-summable physical coefficient sequence into the exact
completed carrier used by the critical mild theory. -/
def weightedLatticeOfCoefficients (c : LatticeMode → ComplexSpace)
    (hc : LatticeWeightedL1 c) : WeightedLatticeBanach :=
  ⟨fun m => latticeModeWeight m • complexEuclideanPoint (c m),
    memℓp_gen (by
      change Summable (fun m : LatticeMode =>
        latticeModeWeight m * ‖complexEuclideanPoint (c m)‖) at hc
      have hs : Summable fun m : LatticeMode =>
          ‖latticeModeWeight m • complexEuclideanPoint (c m)‖ := by
        convert hc using 1
        funext m
        rw [norm_smul,
          Real.norm_of_nonneg (zero_le_one.trans (one_le_latticeModeWeight m))]
      simpa using hs)⟩

/-- Encoding followed by the repository's existing decoder is exactly the
identity on physical coefficients. -/
theorem weightedLatticeCoefficient_ofCoefficients
    (c : LatticeMode → ComplexSpace) (hc : LatticeWeightedL1 c)
    (m : LatticeMode) :
    weightedLatticeCoefficient (weightedLatticeOfCoefficients c hc) m = c m := by
  unfold weightedLatticeCoefficient weightedLatticeOfCoefficients
  rw [smul_smul]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  rw [inv_mul_cancel₀ hm, one_smul]
  simp [complexEuclideanPoint]

theorem latticeHermitian_weightedLatticeOfCoefficients
    (c : LatticeMode → ComplexSpace) (hc : LatticeWeightedL1 c)
    (hconj : ∀ m : LatticeMode, c (-m) = complexConjugate (c m)) :
    LatticeHermitian (weightedLatticeOfCoefficients c hc) := by
  intro m
  rw [weightedLatticeCoefficient_ofCoefficients,
    weightedLatticeCoefficient_ofCoefficients]
  exact hconj m

/-- The official smooth periodic datum, encoded into the actual completed
critical mild carrier using its native integral Fourier coefficients. -/
def nativeInitialCarrier (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    WeightedLatticeBanach :=
  weightedLatticeOfCoefficients (nativeCoefficient u₀)
    (periodicInitialDatum_latticeWeightedL1 hu₀)

theorem nativeInitialCarrier_coefficient (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) (m : LatticeMode) :
    weightedLatticeCoefficient (nativeInitialCarrier u₀ hu₀) m =
      nativeCoefficient u₀ m :=
  weightedLatticeCoefficient_ofCoefficients _ _ _

/-- The precise remaining reality input for the native integral coefficients.
It is isolated independently of convergence and carrier construction. -/
def NativeCoefficientHermitian (u₀ : VelocityField) : Prop :=
  ∀ m : LatticeMode,
    nativeCoefficient u₀ (-m) = complexConjugate (nativeCoefficient u₀ m)

theorem nativeInitialCarrier_hermitian (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) (hconj : NativeCoefficientHermitian u₀) :
    LatticeHermitian (nativeInitialCarrier u₀ hu₀) :=
  latticeHermitian_weightedLatticeOfCoefficients _ _ hconj

/-- The initialized physical field is the convergent real Fourier series of
the official datum's literal nested-integral coefficients. -/
def nativeInitialReconstruction (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) : VelocityField :=
  physicalFourierReconstruction (nativeInitialCarrier u₀ hu₀)

theorem nativeInitialReconstruction_eq_series (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) (x : Space) (i : Fin 3) :
    nativeInitialReconstruction u₀ hu₀ x i =
      ((∑' m : LatticeMode,
        latticeCharacter m x • complexEuclideanPoint (nativeCoefficient u₀ m)) i).re := by
  have hseries : complexFourierReconstruction (nativeInitialCarrier u₀ hu₀) x =
      ∑' m : LatticeMode,
        latticeCharacter m x • complexEuclideanPoint (nativeCoefficient u₀ m) := by
    unfold complexFourierReconstruction
    apply tsum_congr
    intro m
    unfold latticeFourierTerm
    rw [nativeInitialCarrier_coefficient]
  unfold nativeInitialReconstruction physicalFourierReconstruction
  rw [hseries]

theorem continuous_nativeInitialReconstruction (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) :
    Continuous (nativeInitialReconstruction u₀ hu₀) :=
  continuous_physicalFourierReconstruction _

theorem nativeInitialReconstruction_periodic (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) :
    SpatiallyPeriodicDatum (nativeInitialReconstruction u₀ hu₀) :=
  physicalFourierReconstruction_periodic _

theorem nativeInitialReconstruction_exactly_real (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) (hconj : NativeCoefficientHermitian u₀)
    (x : Space) :
    complexEuclideanPoint (complexOfReal (nativeInitialReconstruction u₀ hu₀ x)) =
      complexFourierReconstruction (nativeInitialCarrier u₀ hu₀) x :=
  complexOfReal_physicalFourierReconstruction
    (nativeInitialCarrier_hermitian u₀ hu₀ hconj) x

end Navier.Analysis.PeriodicFourierReconstruction

#check @Navier.ProblemStatements.PeriodicGlobalRegularity
#print Navier.ProblemStatements.PeriodicGlobalRegularity
#check @Navier.Analysis.PeriodicDatumFourierBridge.periodicInitialDatum_latticeWeightedL1
#check @Navier.Analysis.PeriodicFourierReconstruction.nativeInitialCarrier
#check @Navier.Analysis.PeriodicFourierReconstruction.nativeInitialReconstruction_eq_series
#check @Navier.Analysis.PeriodicFourierReconstruction.nativeInitialReconstruction_exactly_real

#print axioms Navier.Analysis.PeriodicFourierReconstruction.continuous_complexFourierReconstruction
#print axioms Navier.Analysis.PeriodicFourierReconstruction.norm_complexFourierReconstruction_le
#print axioms Navier.Analysis.PeriodicFourierReconstruction.complexFourierReconstruction_periodic
#print axioms Navier.Analysis.PeriodicFourierReconstruction.star_complexFourierReconstruction_apply
#print axioms Navier.Analysis.PeriodicFourierReconstruction.complexOfReal_physicalFourierReconstruction
#print axioms Navier.Analysis.PeriodicFourierReconstruction.weightedLatticeCoefficient_ofCoefficients
#print axioms Navier.Analysis.PeriodicFourierReconstruction.nativeInitialCarrier_coefficient
#print axioms Navier.Analysis.PeriodicFourierReconstruction.nativeInitialReconstruction_eq_series
#print axioms Navier.Analysis.PeriodicFourierReconstruction.nativeInitialReconstruction_exactly_real
