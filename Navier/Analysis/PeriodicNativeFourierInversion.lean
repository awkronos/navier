import Navier.Analysis.PeriodicFourierReconstruction

/-!
# Native Fourier inversion for official periodic data

This module proves that the literal nested unit-cube coefficients constructed
from an official smooth unit-periodic datum reconstruct that datum pointwise.
It uses Mathlib's Fourier inversion on the unit circle and the unit two-torus,
then identifies the product character with the three-torus character used by
`PeriodicFourierReconstruction` and reindexes the absolutely convergent double
series.  No inversion hypothesis is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ContDiff
open Set Filter Topology

namespace Navier.Analysis.PeriodicNativeFourierInversion

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.PeriodicDatumFourierBridge
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Construction
open Navier.Construction.TorusInverse

abbrev PlaneMode := TorusInverse.Frequency

/-- The native three-torus character factors into the first-circle character
and the native two-torus character in the coefficient convention. -/
theorem latticeCharacter_split (n : ℤ) (k : PlaneMode) (x : Space) :
    latticeCharacter (n, k) x =
      fourier n (x 0 : UnitAddCircle) *
        TorusInverse.torusMode k (x 1, x 2) := by
  simp [latticeCharacter, latticeTorusIndex, unitTorusPoint,
    UnitAddTorus.mFourier, TorusInverse.torusMode, Fin.prod_univ_succ]

/-- Descend a continuous one-periodic function to Mathlib's native unit
circle. -/
def circleDescend (g : ℝ → ℂ) (hg : Function.Periodic g 1) : UnitAddCircle → ℂ :=
  hg.lift

@[simp] theorem circleDescend_coe (g : ℝ → ℂ)
    (hg : Function.Periodic g 1) (x : ℝ) :
    circleDescend g hg (x : UnitAddCircle) = g x :=
  hg.lift_coe x

theorem continuous_circleDescend {g : ℝ → ℂ}
    (hg : Function.Periodic g 1) (hgc : Continuous g) :
    Continuous (circleDescend g hg) := by
  apply QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
  simpa [Function.comp_def] using hgc

def circleDescendContinuous (g : ℝ → ℂ) (hg : Function.Periodic g 1)
    (hgc : Continuous g) : C(UnitAddCircle, ℂ) where
  toFun := circleDescend g hg
  continuous_toFun := continuous_circleDescend hg hgc

@[simp] theorem circleDescendContinuous_coe (g : ℝ → ℂ)
    (hg : Function.Periodic g 1) (hgc : Continuous g) (x : ℝ) :
    circleDescendContinuous g hg hgc (x : UnitAddCircle) = g x :=
  circleDescend_coe g hg x

/-- The unit-circle Fourier coefficient of the descended function is exactly
the existing literal unit-interval coefficient. -/
theorem fourierCoeff_circleDescendContinuous (g : ℝ → ℂ)
    (hg : Function.Periodic g 1) (hgc : Continuous g) (n : ℤ) :
    fourierCoeff (circleDescendContinuous g hg hgc) n =
      SmoothFourierData.unitCoeff g n := by
  symm
  simpa using SmoothFourierData.unitCoeff_torusLift
    (circleDescendContinuous g hg hgc) n

/-- The planar Fourier coefficient of a parameter-periodic source is itself
one-periodic in the external parameter. -/
theorem parameterCoefficient_periodic {f : ParametricTorusInverse.Source}
    (hp : UnitPeriodic3 f) (k : PlaneMode) :
    Function.Periodic (fun z => ParametricTorusInverse.coefficient f z k) 1 := by
  intro z
  unfold ParametricTorusInverse.coefficient ParametricTorusInverse.slice
  have heq : (fun Y => f (z + 1, Y)) = fun Y => f (z, Y) := by
    funext Y
    exact hp.2 z Y
  change SmoothFourierData.coefficient (fun Y => f (z + 1, Y)) k =
    SmoothFourierData.coefficient (fun Y => f (z, Y)) k
  rw [heq]

theorem parameterCoefficient_continuous {f : ParametricTorusInverse.Source}
    (hf : ContDiff ℝ ∞ f) (k : PlaneMode) :
    Continuous (fun z => ParametricTorusInverse.coefficient f z k) :=
  (ParametricTorusInverse.coefficient_smooth hf k).continuous

/-- Weighted summability of the native vector coefficients implies absolute
summability of every scalar coordinate. -/
theorem summable_nativeCoefficient_coordinate {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (i : Fin 3) :
    Summable fun m : LatticeMode => ‖nativeCoefficient u₀ m i‖ := by
  have hw := periodicInitialDatum_latticeWeightedL1 hu₀
  have he : Summable fun m : LatticeMode =>
      complexEuclideanNorm (nativeCoefficient u₀ m) := by
    exact hw.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => le_mul_of_one_le_left (norm_nonneg _)
        (one_le_latticeModeWeight m))
  exact he.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => by
      simpa [complexEuclideanNorm] using
        PiLp.norm_apply_le (complexEuclideanPoint (nativeCoefficient u₀ m)) i)

/-- For each fixed planar mode, the literal external-coordinate coefficients
are absolutely summable. -/
theorem summable_scalarCoefficient_firstMode {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (i : Fin 3) (k : PlaneMode) :
    Summable fun n : ℤ =>
      ‖scalarCoefficient (nativeScalarSource u₀ i) (n, k)‖ := by
  have hs := (summable_nativeCoefficient_coordinate hu₀ i).comp_injective
    (i := fun n : ℤ => (n, k)) (fun _ _ h => congrArg Prod.fst h)
  simpa [Function.comp_def, nativeCoefficient, nativeCoefficient_apply] using hs

/-- Unit-circle inversion reconstructs each actual planar coefficient as a
sum over the external lattice frequency. -/
theorem hasSum_firstMode_nativeCoefficient {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (i : Fin 3) (k : PlaneMode) (z : ℝ) :
    HasSum (fun n : ℤ =>
      fourier n (z : UnitAddCircle) * nativeCoefficient u₀ (n, k) i)
      (ParametricTorusInverse.coefficient (nativeScalarSource u₀ i) z k) := by
  let g : ℝ → ℂ := fun q =>
    ParametricTorusInverse.coefficient (nativeScalarSource u₀ i) q k
  have hf : ContDiff ℝ ∞ (nativeScalarSource u₀ i) :=
    nativeScalarSource_smooth hu₀.1 i
  have hp : UnitPeriodic3 (nativeScalarSource u₀ i) :=
    nativeScalarSource_periodic hu₀.2.2 i
  have hgp : Function.Periodic g 1 := parameterCoefficient_periodic hp k
  have hgc : Continuous g := parameterCoefficient_continuous hf k
  have hunit : Summable fun n : ℤ => ‖SmoothFourierData.unitCoeff g n‖ := by
    simpa [g, scalarCoefficient] using
      summable_scalarCoefficient_firstMode hu₀ i k
  have hfourier : Summable fun n : ℤ =>
      fourierCoeff (circleDescendContinuous g hgp hgc) n := by
    apply Summable.of_norm
    simpa only [fourierCoeff_circleDescendContinuous] using hunit
  have hsum := has_pointwise_sum_fourier_series_of_summable hfourier
    (z : UnitAddCircle)
  simp_rw [fourierCoeff_circleDescendContinuous] at hsum
  simpa [g, scalarCoefficient, nativeCoefficient, smul_eq_mul, mul_comm] using hsum

theorem summable_nativeFourierScalarTerm {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (i : Fin 3) (x : Space) :
    Summable fun m : LatticeMode =>
      latticeCharacter m x * nativeCoefficient u₀ m i := by
  apply Summable.of_norm
  simpa [norm_mul, norm_latticeCharacter] using
    summable_nativeCoefficient_coordinate hu₀ i

/-- The one-dimensional inversion result with the native three-torus
character factored exactly into circle and plane characters. -/
theorem hasSum_firstMode_latticeTerm {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (i : Fin 3) (k : PlaneMode) (x : Space) :
    HasSum (fun n : ℤ =>
      latticeCharacter (n, k) x * nativeCoefficient u₀ (n, k) i)
      (TorusInverse.torusMode k (x 1, x 2) *
        ParametricTorusInverse.coefficient (nativeScalarSource u₀ i) (x 0) k) := by
  simpa only [latticeCharacter_split, mul_assoc, mul_left_comm, mul_comm] using
    (hasSum_firstMode_nativeCoefficient hu₀ i k (x 0)).mul_left
      (TorusInverse.torusMode k (x 1, x 2))

/-- The literal nested unit-cube coefficients reconstruct every complexified
coordinate of the official datum.  Absolute convergence justifies the
reindex from `ℤ × ℤ²` to `ℤ² × ℤ`. -/
theorem tsum_latticeCharacter_nativeCoefficient {u₀ : VelocityField}
    (hu₀ : PeriodicInitialDatum u₀) (x : Space) (i : Fin 3) :
    (∑' m : LatticeMode,
      latticeCharacter m x * nativeCoefficient u₀ m i) = (u₀ x i : ℂ) := by
  let F : ℤ × PlaneMode → ℂ := fun m =>
    latticeCharacter m x * nativeCoefficient u₀ m i
  let G : PlaneMode × ℤ → ℂ := fun q => F (q.2, q.1)
  have hF : Summable F := summable_nativeFourierScalarTerm hu₀ i x
  have hG : Summable G := by
    exact (Equiv.prodComm PlaneMode ℤ).summable_iff.mpr hF
  calc
    (∑' m : LatticeMode,
        latticeCharacter m x * nativeCoefficient u₀ m i) =
        ∑' q : PlaneMode × ℤ, G q := by
      exact ((Equiv.prodComm PlaneMode ℤ).tsum_eq F).symm
    _ = ∑' k : PlaneMode, ∑' n : ℤ, G (k, n) := hG.tsum_prod
    _ = ∑' k : PlaneMode,
        TorusInverse.torusMode k (x 1, x 2) *
          ParametricTorusInverse.coefficient
            (nativeScalarSource u₀ i) (x 0) k := by
      apply tsum_congr
      intro k
      exact (hasSum_firstMode_latticeTerm hu₀ i k x).tsum_eq
    _ = TorusInverse.series
        (SmoothFourierData.coefficient
          (ParametricTorusInverse.slice (nativeScalarSource u₀ i) (x 0)))
        (x 1, x 2) := by
      unfold TorusInverse.series
      apply tsum_congr
      intro k
      unfold ParametricTorusInverse.coefficient
      rw [TorusInverse.mode_eq_torusMode]
      ring
    _ = (nativeScalarSource u₀ i) (x 0, (x 1, x 2)) := by
      apply SmoothFourierData.series_coefficient
      · exact (nativeScalarSource_smooth hu₀.1 i).comp
          (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
      · exact (nativeScalarSource_periodic hu₀.2.2 i).1 (x 0)
    _ = (u₀ x i : ℂ) := by
      have hx : (![x 0, x 1, x 2] : Space) = x := by
        ext j
        fin_cases j <;> rfl
      simp [nativeScalarSource, pointToSpace, hx]

/-- The full complex Fourier reconstruction of the initialized carrier is the
coordinatewise complexification of the official real datum. -/
theorem complexFourierReconstruction_nativeInitialCarrier_eq
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) (x : Space) :
    complexFourierReconstruction (nativeInitialCarrier u₀ hu₀) x =
      complexEuclideanPoint (complexOfReal (u₀ x)) := by
  have hterm : (fun m : LatticeMode =>
      latticeFourierTerm (nativeInitialCarrier u₀ hu₀) m x) =
      fun m : LatticeMode =>
        latticeCharacter m x • complexEuclideanPoint (nativeCoefficient u₀ m) := by
    funext m
    unfold latticeFourierTerm
    rw [nativeInitialCarrier_coefficient]
  have hv : Summable fun m : LatticeMode =>
      latticeCharacter m x • complexEuclideanPoint (nativeCoefficient u₀ m) := by
    have hbase := summable_latticeFourierTerm (nativeInitialCarrier u₀ hu₀) x
    rwa [hterm] at hbase
  ext i
  unfold complexFourierReconstruction
  rw [hterm]
  have hcoord := (complexE3CoordinateCLM i).map_tsum hv
  change complexE3CoordinateCLM i (∑' m : LatticeMode,
    latticeCharacter m x • complexEuclideanPoint (nativeCoefficient u₀ m)) =
      complexEuclideanPoint (complexOfReal (u₀ x)) i
  rw [hcoord]
  simpa [complexE3CoordinateCLM, complexOfReal, complexOfParts] using
    tsum_latticeCharacter_nativeCoefficient hu₀ x i

/-- **Native initial reconstruction.**  Encoding the official periodic datum
by its literal nested unit-cube coefficients and then applying the physical
Fourier reconstruction returns the original datum pointwise. -/
theorem nativeInitialReconstruction_eq (u₀ : VelocityField)
    (hu₀ : PeriodicInitialDatum u₀) :
    nativeInitialReconstruction u₀ hu₀ = u₀ := by
  funext x i
  have h := congrArg (fun z : ComplexE3 => (z i).re)
    (complexFourierReconstruction_nativeInitialCarrier_eq u₀ hu₀ x)
  simpa [nativeInitialReconstruction, physicalFourierReconstruction,
    complexOfReal, complexOfParts] using h

end Navier.Analysis.PeriodicNativeFourierInversion
