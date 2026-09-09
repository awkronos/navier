import Navier.Analysis.PeriodicPressureRecovery
import Navier.Analysis.CriticalMildWeightedBilinear
import Navier.Analysis.CriticalMildMeanDriftRemoval
import Navier.Analysis.PeriodicFourierReconstruction
import Navier.Analysis.PeriodicNativeFourierInversion
import Navier.Analysis.PeriodicDatumFourierConstraints
import Navier.Analysis.CriticalMildFullPositiveTimeRegularity
import Navier.Analysis.CoordinatePDEBridge
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# From the raw critical mild carrier to physical period-one fields

The critical mild fixed-point system is written in a rotated Fourier variable
`A = -2π i û`.  This file records that normalization in Lean, reconstructs the
physical velocity `û = i A/(2π)`, and proves exact initial reconstruction,
Fourier reality, incompressible mode cancellation, period-one spatial
periodicity, and joint smoothness from explicit summable derivative majorants.

The recovered pressure uses the repository's literal countable transport
convolution and the period-one multipliers `2π i k` and
`ν (2π)² |k|²`.  No classical-solution premise is hidden in the regularity
contracts below: they quantify smoothness and summable bounds for the actual
Fourier mode functions.  Deriving every such bound and the strong projected
coefficient equation from the global mild fixed point remains the analytic
boundary needed for the official periodic endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators ContDiff Topology

namespace Navier.Analysis.PeriodicMildClassicalRealization

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildMeanDriftRemoval
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicNativeFourierInversion
open Navier.Analysis.PeriodicDatumFourierConstraints
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.CriticalMildFullPositiveTimeRegularity

theorem latticeCharacter_eq_exp (m : LatticeMode) (x : Space) :
    latticeCharacter m x = Complex.exp
      (periodOneDerivative * ∑ i : Fin 3,
        (latticeFrequency m i : ℂ) * (x i : ℂ)) := by
  simp [latticeCharacter, unitTorusPoint, latticeTorusIndex,
    UnitAddTorus.mFourier, periodOneDerivative,
    latticeFrequency, Fin.prod_univ_succ, Fin.sum_univ_three]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem latticeCharacter_line (m : LatticeMode) (x : Space)
    (j : Fin 3) (s : ℝ) :
    latticeCharacter m (x + s • basisVector j) =
      latticeCharacter m x *
        Complex.exp (periodOneDerivative * (latticeFrequency m j : ℂ) * s) := by
  classical
  rw [latticeCharacter_eq_exp, latticeCharacter_eq_exp, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, Complex.ofReal_add,
    Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [basisVector]
    ring
  · intro b _hb hbj
    simp [basisVector, hbj]
  · simp

theorem hasDerivAt_latticeCharacter_line (m : LatticeMode) (x : Space)
    (j : Fin 3) (s : ℝ) :
    HasDerivAt (fun s : ℝ => latticeCharacter m (x + s • basisVector j))
      (periodOneDerivative * (latticeFrequency m j : ℂ) *
        latticeCharacter m (x + s • basisVector j)) s := by
  have he : (fun s : ℝ => latticeCharacter m (x + s • basisVector j)) =
      fun s : ℝ => latticeCharacter m x *
        Complex.exp (periodOneDerivative * (latticeFrequency m j : ℂ) * s) := by
    funext s
    exact latticeCharacter_line m x j s
  rw [he]
  have h :=
    (((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul
      (periodOneDerivative * (latticeFrequency m j : ℂ))).cexp.const_mul
        (latticeCharacter m x))
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one,
    latticeCharacter_line, one_mul, mul_one, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- One scalar coordinate of the actual time-dependent Fourier series. -/
def complexVelocityCoordinate (a : ℝ → WeightedLatticeBanach)
    (t : ℝ) (x : Space) (i : Fin 3) : ℂ :=
  ∑' m : LatticeMode,
    latticeCharacter m x * weightedLatticeCoefficient (a t) m i

/-- The physical velocity obtained from the real part of the completed
time-dependent lattice series. -/
def reconstructedVelocity (a : ℝ → WeightedLatticeBanach) : VelocityEvolution :=
  fun t x i => (complexVelocityCoordinate a t x i).re

/-- The coefficient rotation from the repository's raw mild variable `A` to
the physical period-one Fourier coefficient `û`. -/
def rawToPhysicalAmplitude : ℂ := Complex.I / (2 * Real.pi : ℂ)

/-- The inverse coefficient rotation `û ↦ A = -2π i û`. -/
def physicalToRawAmplitude : ℂ := -(2 * Real.pi : ℂ) * Complex.I

theorem rawToPhysicalAmplitude_mul_physicalToRawAmplitude :
    rawToPhysicalAmplitude * physicalToRawAmplitude = 1 := by
  unfold rawToPhysicalAmplitude physicalToRawAmplitude
  field_simp [Real.pi_ne_zero]
  rw [Complex.I_sq]
  norm_num

theorem physicalToRawAmplitude_mul_rawToPhysicalAmplitude :
    physicalToRawAmplitude * rawToPhysicalAmplitude = 1 := by
  rw [mul_comm, rawToPhysicalAmplitude_mul_physicalToRawAmplitude]

theorem rawFourierScale_eq_physicalToRawAmplitude :
    rawFourierScale = physicalToRawAmplitude := by
  unfold rawFourierScale physicalToRawAmplitude
  ring

theorem star_rawToPhysicalAmplitude :
    star rawToPhysicalAmplitude = -rawToPhysicalAmplitude := by
  unfold rawToPhysicalAmplitude
  simp
  ring

theorem star_physicalToRawAmplitude :
    star physicalToRawAmplitude = -physicalToRawAmplitude := by
  unfold physicalToRawAmplitude
  simp

/-- The viscosity passed to the raw mild equation for a physical period-one
viscosity `ν`. -/
def rawMildViscosity (ν : ℝ) : ℝ := ν * (2 * Real.pi) ^ 2

/-- Decode a raw critical-mild carrier into physical period-one coefficients. -/
def physicalCarrier (A : WeightedLatticeBanach) : WeightedLatticeBanach :=
  rawToPhysicalAmplitude • A

theorem rawCarrierOfPhysical_physicalCarrier
    (A : WeightedLatticeBanach) :
    rawCarrierOfPhysical (physicalCarrier A) = A := by
  unfold rawCarrierOfPhysical physicalCarrier
  rw [rawFourierScale_eq_physicalToRawAmplitude, smul_smul,
    physicalToRawAmplitude_mul_rawToPhysicalAmplitude, one_smul]

/-- The strong coefficient equation obtained by differentiating the raw mild
identity.  This is an explicit Fourier ODE premise: it contains the actual
repository convolution, Leray multiplier, raw viscosity, and decoded
coefficient. -/
def RawProjectedModeEquation (ν : ℝ)
    (A : ℝ → WeightedLatticeBanach)
    (rawTimeDerivative : ℝ → LatticeMode → ComplexSpace) : Prop :=
  ∀ t k,
    rawTimeDerivative t k -
        complexLeray (latticeFrequency k)
          (spectralOutputCoefficient k (A t) (A t)) +
        (((rawMildViscosity ν) *
          (latticeFrequency k ⬝ᵥ latticeFrequency k) : ℝ) : ℂ) •
          weightedLatticeCoefficient (A t) k = 0

/-- Exact nonlinear normalization: after decoding `A` to `û`, the negative
raw convolution term becomes the physical period-one `2π i` convection term.
The proof consumes the literal bilinear scaling theorem for
`spectralOutputCoefficient`. -/
theorem rawNonlinearity_to_periodOneConvection
    (k : LatticeMode) (A : WeightedLatticeBanach) :
    rawToPhysicalAmplitude •
        (-complexLeray (latticeFrequency k)
          (spectralOutputCoefficient k A A)) =
      complexLeray (latticeFrequency k)
        (periodOneConvectionCoefficient k
          (physicalCarrier A) (physicalCarrier A)) := by
  change rawToPhysicalAmplitude •
        (-complexLeray (latticeFrequency k)
          (spectralOutputCoefficient k A A)) =
      complexLeray (latticeFrequency k)
        (periodOneDerivative • spectralOutputCoefficient k
          (physicalCarrier A) (physicalCarrier A))
  have hs := spectralOutputCoefficient_rawCarrierOfPhysical_eq
    k (physicalCarrier A) (physicalCarrier A)
  rw [rawCarrierOfPhysical_physicalCarrier] at hs
  rw [hs]
  rw [(complexLeray (latticeFrequency k)).map_smul
    (-((2 * Real.pi) ^ 2 : ℝ) : ℂ)
    (spectralOutputCoefficient k (physicalCarrier A) (physicalCarrier A))]
  rw [(complexLeray (latticeFrequency k)).map_smul
    periodOneDerivative
    (spectralOutputCoefficient k (physicalCarrier A) (physicalCarrier A))]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  unfold rawToPhysicalAmplitude periodOneDerivative
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

/-- Exact viscous normalization `μ=ν(2π)²` under the physical decoder. -/
theorem rawViscosity_to_periodOneViscosity
    (ν : ℝ) (k : LatticeMode) (A : WeightedLatticeBanach) :
    rawToPhysicalAmplitude •
        ((((rawMildViscosity ν) *
          (latticeFrequency k ⬝ᵥ latticeFrequency k) : ℝ) : ℂ) •
          weightedLatticeCoefficient A k) =
      periodOneViscousCoefficient ν k
        (weightedLatticeCoefficient (physicalCarrier A) k) := by
  unfold periodOneViscousCoefficient rawMildViscosity physicalCarrier
  rw [congrFun (weightedLatticeCoefficient_smul rawToPhysicalAmplitude A) k]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- A strong raw coefficient equation becomes the exactly normalized
period-one projected Navier--Stokes coefficient equation. -/
theorem rawProjectedModeEquation_to_physicalProjected
    (ν : ℝ) (A : ℝ → WeightedLatticeBanach)
    (rawTimeDerivative : ℝ → LatticeMode → ComplexSpace)
    (hraw : RawProjectedModeEquation ν A rawTimeDerivative)
    (t : ℝ) (k : LatticeMode) :
    rawToPhysicalAmplitude • rawTimeDerivative t k +
        complexLeray (latticeFrequency k)
          (periodOneConvectionCoefficient k
            (physicalCarrier (A t)) (physicalCarrier (A t))) +
        periodOneViscousCoefficient ν k
          (weightedLatticeCoefficient (physicalCarrier (A t)) k) = 0 := by
  have hr := hraw t k
  rw [sub_eq_add_neg] at hr
  have hs := congrArg (fun z : ComplexSpace => rawToPhysicalAmplitude • z) hr
  simp only [smul_add, smul_zero] at hs
  rw [rawNonlinearity_to_periodOneConvection,
    rawViscosity_to_periodOneViscosity] at hs
  exact hs

/-- The normalized raw strong equation, together with the explicit recovered
pressure multiplier, yields the literal unprojected period-one coefficient
equation. -/
theorem rawProjectedModeEquation_to_physicalUnprojected
    (ν : ℝ) (A : ℝ → WeightedLatticeBanach)
    (rawTimeDerivative : ℝ → LatticeMode → ComplexSpace)
    (hraw : RawProjectedModeEquation ν A rawTimeDerivative)
    (t : ℝ) (k : LatticeMode) :
    rawToPhysicalAmplitude • rawTimeDerivative t k +
        periodOneConvectionCoefficient k
          (physicalCarrier (A t)) (physicalCarrier (A t)) +
        periodOneViscousCoefficient ν k
          (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
        periodOneGradientCoefficient k
          (periodOnePressureCoefficient k
            (physicalCarrier (A t)) (physicalCarrier (A t))) = 0 := by
  exact projected_mode_equation_to_unprojected ν k
    (rawToPhysicalAmplitude • rawTimeDerivative t k)
    (weightedLatticeCoefficient (physicalCarrier (A t)) k)
    (physicalCarrier (A t)) (physicalCarrier (A t))
    (rawProjectedModeEquation_to_physicalProjected
      ν A rawTimeDerivative hraw t k)

/-- The physical decoder preserves the fixed-time two-spatial-derivative
summability threshold obtained from the actual positive-time mild equation. -/
theorem summable_twoSpatialDerivatives_physicalCarrier
    {A : WeightedLatticeBanach}
    (hA : Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient A k)) :
    Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient (physicalCarrier A) k) := by
  have hscaled := hA.mul_left ‖rawToPhysicalAmplitude‖
  apply hscaled.congr
  intro k
  unfold physicalCarrier complexEuclideanNorm
  rw [congrFun (weightedLatticeCoefficient_smul rawToPhysicalAmplitude A) k,
    Pi.smul_apply, complexEuclideanPoint_smul, norm_smul]
  ring

/-- The actual mild trajectory, decoded with the physical `i/(2π)`
normalization, has two absolutely summable spatial Fourier derivatives at
every positive time for which the local mild chart and bound are available. -/
theorem mildTrajectory_physicalCarrier_twoSpatialDerivatives
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (hu₀ : CriticalMildDuhamelBochner.LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, CriticalMildDuhamelBochner.LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) t),
      u s = CriticalMildSelfMap.criticalMildImage
        ν hν u₀ u hu s hs.1) :
    Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm
          (weightedLatticeCoefficient (physicalCarrier (u t)) k) :=
  summable_twoSpatialDerivatives_physicalCarrier
    (mildTrajectory_decoded_twoSpatialDerivatives
      ν hν u₀ hu₀ u huc hu hR ht huR hmild)

/-- Initialize the raw critical-mild variable from the exact native Fourier
carrier of the official datum. -/
def rawInitialCarrier (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    WeightedLatticeBanach :=
  physicalToRawAmplitude • nativeInitialCarrier u₀ hu₀

theorem physicalCarrier_rawInitialCarrier
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    physicalCarrier (rawInitialCarrier u₀ hu₀) = nativeInitialCarrier u₀ hu₀ := by
  unfold physicalCarrier rawInitialCarrier
  rw [smul_smul, rawToPhysicalAmplitude_mul_physicalToRawAmplitude, one_smul]

/-- Actual physical velocity reconstructed from a raw mild-carrier path. -/
def physicalMildVelocity (A : ℝ → WeightedLatticeBanach) : VelocityEvolution :=
  reconstructedVelocity (fun t => physicalCarrier (A t))

/-- The raw reality condition transported by the plus-sign mild equation.
It differs by one minus sign from physical Hermitian symmetry. -/
def LatticeAntiHermitian (A : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode,
    weightedLatticeCoefficient A (-m) =
      -complexConjugate (weightedLatticeCoefficient A m)

theorem latticeAntiHermitian_physicalToRawCarrier
    {u : WeightedLatticeBanach} (hu : LatticeHermitian u) :
    LatticeAntiHermitian (physicalToRawAmplitude • u) := by
  intro m
  have hsmul := weightedLatticeCoefficient_smul physicalToRawAmplitude u
  rw [congrFun hsmul (-m), congrFun hsmul m]
  change physicalToRawAmplitude • weightedLatticeCoefficient u (-m) =
    -complexConjugate
      (physicalToRawAmplitude • weightedLatticeCoefficient u m)
  rw [hu m]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, complexConjugate, smul_eq_mul]
  rw [map_mul]
  have hs : (starRingEnd ℂ) physicalToRawAmplitude =
      -physicalToRawAmplitude := star_physicalToRawAmplitude
  rw [hs]
  ring

theorem latticeAntiHermitian_rawInitialCarrier
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    LatticeAntiHermitian (rawInitialCarrier u₀ hu₀) := by
  unfold rawInitialCarrier
  exact latticeAntiHermitian_physicalToRawCarrier
    (nativeInitialCarrier_hermitian u₀ hu₀ (nativeCoefficient_hermitian u₀))

/-- The normalized raw initializer lies in the exact transverse carrier used
by the critical mild equation. -/
theorem latticeDivergenceFree_rawInitialCarrier
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    CriticalMildDuhamelBochner.LatticeDivergenceFree
      (rawInitialCarrier u₀ hu₀) := by
  intro m
  unfold rawInitialCarrier
  rw [congrFun
    (weightedLatticeCoefficient_smul physicalToRawAmplitude
      (nativeInitialCarrier u₀ hu₀)) m]
  change inner ℂ (complexFrequency (latticeFrequency m))
    (physicalToRawAmplitude •
      complexEuclideanPoint
        (weightedLatticeCoefficient (nativeInitialCarrier u₀ hu₀) m)) = 0
  rw [inner_smul_right,
    nativeInitialCarrier_divergenceFree u₀ hu₀ m, mul_zero]

/-- Multiplication by `i/(2π)` converts raw anti-Hermitian coefficients into
the Hermitian symmetry required by a real physical Fourier series. -/
theorem latticeHermitian_physicalCarrier {A : WeightedLatticeBanach}
    (hA : LatticeAntiHermitian A) : LatticeHermitian (physicalCarrier A) := by
  intro m
  unfold physicalCarrier
  have hsmul := weightedLatticeCoefficient_smul rawToPhysicalAmplitude A
  rw [congrFun hsmul (-m), congrFun hsmul m]
  change rawToPhysicalAmplitude • weightedLatticeCoefficient A (-m) =
    complexConjugate
      (rawToPhysicalAmplitude • weightedLatticeCoefficient A m)
  rw [hA m]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, complexConjugate, smul_eq_mul]
  rw [map_mul]
  have hs : (starRingEnd ℂ) rawToPhysicalAmplitude =
      -rawToPhysicalAmplitude := star_rawToPhysicalAmplitude
  rw [hs]
  ring

theorem latticeDivergenceFree_physicalCarrier {A : WeightedLatticeBanach}
    (hA : CriticalMildDuhamelBochner.LatticeDivergenceFree A) :
    CriticalMildDuhamelBochner.LatticeDivergenceFree (physicalCarrier A) := by
  intro m
  unfold physicalCarrier
  rw [congrFun
    (weightedLatticeCoefficient_smul rawToPhysicalAmplitude A) m]
  change inner ℂ (complexFrequency (latticeFrequency m))
    (rawToPhysicalAmplitude •
      complexEuclideanPoint (weightedLatticeCoefficient A m)) = 0
  rw [inner_smul_right, hA m, mul_zero]

theorem reconstructedVelocity_eq_physicalFourierReconstruction
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) :
    reconstructedVelocity a t = physicalFourierReconstruction (a t) := by
  funext x i
  unfold reconstructedVelocity complexVelocityCoordinate
  have hs := summable_latticeFourierTerm (a t) x
  unfold physicalFourierReconstruction complexFourierReconstruction
  apply congrArg Complex.re
  change (∑' m : LatticeMode,
      latticeCharacter m x * weightedLatticeCoefficient (a t) m i) =
    complexE3CoordinateCLM i
      (∑' m : LatticeMode, latticeFourierTerm (a t) m x)
  rw [(complexE3CoordinateCLM i).map_tsum hs]
  apply tsum_congr
  intro m
  rfl

/-- The normalized raw initializer reconstructs the official datum exactly. -/
theorem physicalMildVelocity_rawInitialCarrier_eq
    (u₀ : VelocityField) (hu₀ : PeriodicInitialDatum u₀) :
    physicalMildVelocity (fun _ => rawInitialCarrier u₀ hu₀) 0 = u₀ := by
  rw [physicalMildVelocity, reconstructedVelocity_eq_physicalFourierReconstruction,
    physicalCarrier_rawInitialCarrier]
  change nativeInitialReconstruction u₀ hu₀ = u₀
  exact nativeInitialReconstruction_eq u₀ hu₀

theorem summable_complexVelocityCoordinate_term
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space) (i : Fin 3) :
    Summable fun m : LatticeMode =>
      latticeCharacter m x * weightedLatticeCoefficient (a t) m i := by
  apply Summable.of_norm
  have h := summable_decodedCoefficientNorm (a t)
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    rw [norm_mul, norm_latticeCharacter, one_mul]
    simpa [complexEuclideanNorm] using
      PiLp.norm_apply_le (complexEuclideanPoint
        (weightedLatticeCoefficient (a t) m)) i)

theorem norm_latticeFrequency_coordinate_le_weight
    (m : LatticeMode) (j : Fin 3) :
    ‖(latticeFrequency m j : ℂ)‖ ≤ latticeModeWeight m := by
  calc
    ‖(latticeFrequency m j : ℂ)‖ =
        ‖complexFrequency (latticeFrequency m) j‖ := by simp
    _ ≤ ‖complexFrequency (latticeFrequency m)‖ :=
      PiLp.norm_apply_le (complexFrequency (latticeFrequency m)) j
    _ ≤ latticeModeWeight m := by
      unfold latticeModeWeight
      linarith [norm_nonneg (complexFrequency (latticeFrequency m))]

/-- A single weighted lattice moment controls every first spatial derivative
of the actual physical series. -/
def spatialDerivativeMajorant (u : WeightedLatticeBanach)
    (m : LatticeMode) : ℝ :=
  ‖periodOneDerivative‖ *
    latticeWeightedAmplitude (weightedLatticeCoefficient u) m

theorem summable_spatialDerivativeMajorant (u : WeightedLatticeBanach) :
    Summable (spatialDerivativeMajorant u) := by
  exact (latticeWeightedL1_coefficient u).mul_left ‖periodOneDerivative‖

theorem hasDerivAt_complexVelocityCoordinate_term_line
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space)
    (i j : Fin 3) (m : LatticeMode) (s : ℝ) :
    HasDerivAt
      (fun s : ℝ => latticeCharacter m (x + s • basisVector j) *
        weightedLatticeCoefficient (a t) m i)
      (periodOneDerivative * (latticeFrequency m j : ℂ) *
        latticeCharacter m (x + s • basisVector j) *
          weightedLatticeCoefficient (a t) m i) s :=
  (hasDerivAt_latticeCharacter_line m x j s).mul_const _

theorem norm_complexVelocityCoordinate_term_line_derivative_le
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space)
    (i j : Fin 3) (m : LatticeMode) :
    ‖periodOneDerivative * (latticeFrequency m j : ℂ) *
        latticeCharacter m x * weightedLatticeCoefficient (a t) m i‖ ≤
      spatialDerivativeMajorant (a t) m := by
  rw [norm_mul, norm_mul, norm_mul, norm_latticeCharacter, mul_one]
  unfold spatialDerivativeMajorant latticeWeightedAmplitude
  have hk := norm_latticeFrequency_coordinate_le_weight m j
  have hc : ‖weightedLatticeCoefficient (a t) m i‖ ≤
      complexEuclideanNorm (weightedLatticeCoefficient (a t) m) := by
    simpa [complexEuclideanNorm] using
      PiLp.norm_apply_le (complexEuclideanPoint
        (weightedLatticeCoefficient (a t) m)) i
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hk hc
      (norm_nonneg (weightedLatticeCoefficient (a t) m i))
      (zero_le_one.trans (one_le_latticeModeWeight m)))
    (norm_nonneg periodOneDerivative)

theorem summable_complexVelocityCoordinate_line_derivative
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space)
    (i j : Fin 3) :
    Summable fun m : LatticeMode =>
      periodOneDerivative * (latticeFrequency m j : ℂ) *
        latticeCharacter m x * weightedLatticeCoefficient (a t) m i := by
  exact Summable.of_norm_bounded
    (summable_spatialDerivativeMajorant (a t))
    (fun m => norm_complexVelocityCoordinate_term_line_derivative_le
      a t x i j m)

/-- The trace of the actual differentiated physical Fourier series vanishes
for every transverse carrier.  All finite/infinite sum interchanges are
justified by the one-weight `ℓ¹` carrier. -/
theorem complexDivergenceSeries_eq_zero
    (a : ℝ → WeightedLatticeBanach)
    (ha : ∀ t,
      CriticalMildDuhamelBochner.LatticeDivergenceFree (a t))
    (t : ℝ) (x : Space) :
    (∑' m : LatticeMode, ∑ i : Fin 3,
      periodOneDerivative * (latticeFrequency m i : ℂ) *
        latticeCharacter m x * weightedLatticeCoefficient (a t) m i) = 0 := by
  have hterm : (fun m : LatticeMode => ∑ i : Fin 3,
      periodOneDerivative * (latticeFrequency m i : ℂ) *
        latticeCharacter m x * weightedLatticeCoefficient (a t) m i) =
      fun _ => 0 := by
    funext m
    have htrans := ha t m
    rw [inner_complexFrequency] at htrans
    calc
      (∑ i : Fin 3,
        periodOneDerivative * (latticeFrequency m i : ℂ) *
          latticeCharacter m x * weightedLatticeCoefficient (a t) m i) =
        periodOneDerivative * latticeCharacter m x *
          (∑ i : Fin 3,
            (latticeFrequency m i : ℂ) *
              weightedLatticeCoefficient (a t) m i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
      _ = 0 := by rw [htrans, mul_zero]
  rw [hterm]
  simp

/-- Exact termwise spatial differentiation of the completed complex velocity.
The factor is the physical period-one multiplier `2π i k_j`; taking real
parts yields the corresponding derivative of the physical reconstruction. -/
theorem hasDerivAt_complexVelocityCoordinate_line
    (a : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space)
    (i j : Fin 3) :
    HasDerivAt
      (fun s : ℝ => complexVelocityCoordinate a t
        (x + s • basisVector j) i)
      (∑' m : LatticeMode,
        periodOneDerivative * (latticeFrequency m j : ℂ) *
          latticeCharacter m x * weightedLatticeCoefficient (a t) m i) 0 := by
  let g : LatticeMode → ℝ → ℂ := fun m s =>
    latticeCharacter m (x + s • basisVector j) *
      weightedLatticeCoefficient (a t) m i
  let g' : LatticeMode → ℝ → ℂ := fun m s =>
    periodOneDerivative * (latticeFrequency m j : ℂ) *
      latticeCharacter m (x + s • basisVector j) *
        weightedLatticeCoefficient (a t) m i
  have hcomplex : HasDerivAt
      (fun s : ℝ => ∑' m : LatticeMode, g m s)
      (∑' m : LatticeMode, g' m 0) 0 := by
    exact hasDerivAt_tsum (g := g) (g' := g') (y₀ := 0)
      (summable_spatialDerivativeMajorant (a t))
      (fun m s => by
        dsimp [g, g']
        exact
        hasDerivAt_complexVelocityCoordinate_term_line a t x i j m s)
      (fun m s =>
        norm_complexVelocityCoordinate_term_line_derivative_le
          a t (x + s • basisVector j) i j m)
      (by
        simpa [g] using summable_complexVelocityCoordinate_term a t x i) 0
  simpa only [g, g', complexVelocityCoordinate, zero_smul, add_zero] using hcomplex

/-- The official real coordinate derivative is the real part of the exact
termwise differentiated physical Fourier series. -/
theorem spatialPartial_physicalMildVelocity_eq
    (A : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space)
    (i j : Fin 3) :
    CoordinatePDEBridge.spatialPartial j
        (fun y => physicalMildVelocity A t y i) x =
      (∑' m : LatticeMode,
        periodOneDerivative * (latticeFrequency m j : ℂ) *
          latticeCharacter m x *
            weightedLatticeCoefficient (physicalCarrier (A t)) m i).re := by
  have hc := hasDerivAt_complexVelocityCoordinate_line
    (fun s => physicalCarrier (A s)) t x i j
  have hr : HasDerivAt
      (fun s : ℝ =>
        (complexVelocityCoordinate (fun r => physicalCarrier (A r)) t
          (x + s • basisVector j) i).re)
      (∑' m : LatticeMode,
        periodOneDerivative * (latticeFrequency m j : ℂ) *
          latticeCharacter m x *
            weightedLatticeCoefficient (physicalCarrier (A t)) m i).re 0 := by
    simpa [Function.comp_def] using
      (Complex.reCLM.hasFDerivAt.comp 0 hc.hasFDerivAt).hasDerivAt
  have hline : HasLineDerivAt ℝ
      (fun y => physicalMildVelocity A t y i)
      (∑' m : LatticeMode,
        periodOneDerivative * (latticeFrequency m j : ℂ) *
          latticeCharacter m x *
            weightedLatticeCoefficient (physicalCarrier (A t)) m i).re
      x (basisVector j) := by
    simpa [HasLineDerivAt, physicalMildVelocity, reconstructedVelocity] using hr
  unfold CoordinatePDEBridge.spatialPartial
  exact hline.lineDeriv

/-- Transversality of the raw carrier gives the official coordinatewise
divergence equation for the actual reconstructed physical velocity. -/
theorem officialCoordinateDivergenceFree_physicalMildVelocity
    (A : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ t, CriticalMildDuhamelBochner.LatticeDivergenceFree (A t)) :
    CoordinatePDEBridge.OfficialCoordinateDivergenceFree
      (physicalMildVelocity A) := by
  intro t _ht x
  let f : Fin 3 → LatticeMode → ℂ := fun i m =>
    periodOneDerivative * (latticeFrequency m i : ℂ) *
      latticeCharacter m x *
        weightedLatticeCoefficient (physicalCarrier (A t)) m i
  have hsum (i : Fin 3) : Summable (f i) := by
    simpa [f] using summable_complexVelocityCoordinate_line_derivative
      (fun s => physicalCarrier (A s)) t x i i
  have hinterchange :
      (∑' m : LatticeMode, ∑ i : Fin 3, f i m) =
        ∑ i : Fin 3, ∑' m : LatticeMode, f i m := by
    simpa using Summable.tsum_finsetSum
      (s := Finset.univ) (fun i _hi => hsum i)
  rw [Finset.sum_congr rfl (fun i _hi =>
    spatialPartial_physicalMildVelocity_eq A t x i i)]
  calc
    (∑ i : Fin 3, (∑' m : LatticeMode, f i m).re) =
        (∑ i : Fin 3, ∑' m : LatticeMode, f i m).re := by simp
    _ = (∑' m : LatticeMode, ∑ i : Fin 3, f i m).re := by
      rw [hinterchange]
    _ = 0 := by
      have hz := complexDivergenceSeries_eq_zero
        (fun s => physicalCarrier (A s))
        (fun s => latticeDivergenceFree_physicalCarrier (hdiv s)) t x
      simpa [f] using congrArg Complex.re hz

/-- One mode of the normalized physical spacetime velocity series. -/
def physicalSpacetimeVelocityModeTerm
    (A : ℝ → WeightedLatticeBanach) (m : LatticeMode) (i : Fin 3)
    (z : ℝ × Space) : ℂ :=
  latticeCharacter m z.2 *
    weightedLatticeCoefficient (physicalCarrier (A z.1)) m i

/-- The closed spacetime domain used by the official smoothness predicates. -/
def nonnegativeSpacetime : Set (ℝ × Space) :=
  Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)

/-- Local sufficient coefficient-side contract for joint `C∞` convergence.

At each point of the closed nonnegative-time half-space, every actual Fourier
mode agrees within the half-space with a smooth extension.  Each chosen
extension has global summable derivative majorants, but the extensions and
bounds may change with the base point.  Thus the contract imposes only local
estimates on the actual trajectory and no estimates on its negative-time
values.  At `t = 0`, agreement is required only within the closed half-space. -/
def FourierSpacetimeRapid (A : ℝ → WeightedLatticeBanach) : Prop :=
  ∀ z ∈ nonnegativeSpacetime,
    ∃ G : Fin 3 → LatticeMode → (ℝ × Space → ℂ),
    ∃ M : Fin 3 → ℕ → LatticeMode → ℝ,
      (∀ i m, ContDiff ℝ ∞ (G i m)) ∧
      (∀ i n, Summable (M i n)) ∧
      (∀ i n m y, ‖iteratedFDeriv ℝ n (G i m) y‖ ≤ M i n m) ∧
      ∀ᶠ y in 𝓝[nonnegativeSpacetime] z,
        ∀ i m, G i m y = physicalSpacetimeVelocityModeTerm A m i y

theorem contDiffWithinAt_complexPhysicalVelocityCoordinate
    {A : ℝ → WeightedLatticeBanach} (hA : FourierSpacetimeRapid A)
    {z : ℝ × Space} (hz : z ∈ nonnegativeSpacetime) (i : Fin 3) :
    ContDiffWithinAt ℝ ∞ (fun y : ℝ × Space =>
      ∑' m : LatticeMode, physicalSpacetimeVelocityModeTerm A m i y)
      nonnegativeSpacetime z := by
  rcases hA z hz with ⟨G, M, hsmooth, hM, hbound, hagree⟩
  have hG : ContDiff ℝ ∞ (fun y : ℝ × Space =>
      ∑' m : LatticeMode, G i m y) :=
    contDiff_tsum (fun m => hsmooth i m) (fun n _hn => hM i n)
      (fun n m y _hn => hbound i n m y)
  have heq : (fun y : ℝ × Space =>
      ∑' m : LatticeMode, physicalSpacetimeVelocityModeTerm A m i y) =ᶠ[𝓝[nonnegativeSpacetime] z]
      (fun y : ℝ × Space => ∑' m : LatticeMode, G i m y) := by
    filter_upwards [hagree] with y hy
    exact tsum_congr (fun m => (hy i m).symm)
  exact hG.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq hz

/-- The explicit all-jet Fourier majorants produce the exact official joint
half-space smoothness field for the normalized physical velocity. -/
theorem smoothVelocity_physicalMildVelocity
    {A : ℝ → WeightedLatticeBanach} (hA : FourierSpacetimeRapid A) :
    SmoothVelocityOnNonnegativeTime (physicalMildVelocity A) := by
  intro z hz
  rw [contDiffWithinAt_pi]
  intro i
  change ContDiffWithinAt ℝ ∞ (fun y : ℝ × Space =>
    (∑' m : LatticeMode, physicalSpacetimeVelocityModeTerm A m i y).re)
      nonnegativeSpacetime z
  have hc := contDiffWithinAt_complexPhysicalVelocityCoordinate hA hz i
  have hre : ContDiffWithinAt ℝ ∞
      (fun _ : ℝ × Space => Complex.reCLM) nonnegativeSpacetime z :=
    contDiffWithinAt_const
  simpa using hre.clm_apply hc

/-- Raw mode transversality plus the explicit Fourier all-jet bounds yields
the repository's exact Fréchet-divergence incompressibility predicate. -/
theorem incompressible_physicalMildVelocity
    {A : ℝ → WeightedLatticeBanach} (hA : FourierSpacetimeRapid A)
    (hdiv : ∀ t, CriticalMildDuhamelBochner.LatticeDivergenceFree (A t)) :
    Incompressible (physicalMildVelocity A) := by
  exact (CoordinatePDEBridge.incompressible_iff_officialCoordinateDivergenceFree
    (physicalMildVelocity A) (smoothVelocity_physicalMildVelocity hA)).2
      (officialCoordinateDivergenceFree_physicalMildVelocity A hdiv)

/-- The normalized physical velocity is period one at every time, directly
from the actual Fourier reconstruction. -/
theorem spatiallyPeriodicVelocity_physicalMildVelocity
    (A : ℝ → WeightedLatticeBanach) :
    SpatiallyPeriodicVelocity (physicalMildVelocity A) := by
  intro t _ht
  rw [physicalMildVelocity,
    reconstructedVelocity_eq_physicalFourierReconstruction]
  exact physicalFourierReconstruction_periodic (physicalCarrier (A t))

/-- The actual pressure coefficient recovered from the normalized physical
transport convolution. -/
def physicalPressureCoefficient (A : ℝ → WeightedLatticeBanach)
    (t : ℝ) (m : LatticeMode) : ℂ :=
  periodOnePressureCoefficient m (physicalCarrier (A t))
    (physicalCarrier (A t))

def physicalSpacetimePressureModeTerm
    (A : ℝ → WeightedLatticeBanach) (m : LatticeMode)
    (z : ℝ × Space) : ℂ :=
  latticeCharacter m z.2 * physicalPressureCoefficient A z.1 m

/-- The real zero-mean pressure reconstructed from the exact pressure
multiplier of the physical transport convolution. -/
def physicalMildPressure (A : ℝ → WeightedLatticeBanach) : PressureEvolution :=
  fun t x => (∑' m : LatticeMode,
    physicalSpacetimePressureModeTerm A m (t, x)).re

/-- Local all-jet summability for the recovered pressure series.  At every
point of the closed half-space, the actual pressure modes agree within that
half-space with smooth extensions having summable derivative majorants. -/
def PressureFourierSpacetimeRapid (A : ℝ → WeightedLatticeBanach) : Prop :=
  ∀ z ∈ nonnegativeSpacetime,
    ∃ G : LatticeMode → (ℝ × Space → ℂ),
    ∃ M : ℕ → LatticeMode → ℝ,
      (∀ m, ContDiff ℝ ∞ (G m)) ∧
      (∀ n, Summable (M n)) ∧
      (∀ n m y, ‖iteratedFDeriv ℝ n (G m) y‖ ≤ M n m) ∧
      ∀ᶠ y in 𝓝[nonnegativeSpacetime] z,
        ∀ m, G m y = physicalSpacetimePressureModeTerm A m y

theorem contDiffWithinAt_complexPhysicalPressure
    {A : ℝ → WeightedLatticeBanach} (hA : PressureFourierSpacetimeRapid A)
    {z : ℝ × Space} (hz : z ∈ nonnegativeSpacetime) :
    ContDiffWithinAt ℝ ∞ (fun y : ℝ × Space =>
      ∑' m : LatticeMode, physicalSpacetimePressureModeTerm A m y)
      nonnegativeSpacetime z := by
  rcases hA z hz with ⟨G, M, hsmooth, hM, hbound, hagree⟩
  have hG : ContDiff ℝ ∞ (fun y : ℝ × Space =>
      ∑' m : LatticeMode, G m y) :=
    contDiff_tsum hsmooth (fun n _hn => hM n)
      (fun n m y _hn => hbound n m y)
  have heq : (fun y : ℝ × Space =>
      ∑' m : LatticeMode, physicalSpacetimePressureModeTerm A m y) =ᶠ[𝓝[nonnegativeSpacetime] z]
      (fun y : ℝ × Space => ∑' m : LatticeMode, G m y) := by
    filter_upwards [hagree] with y hy
    exact tsum_congr (fun m => (hy m).symm)
  exact hG.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq hz

theorem smoothPressure_physicalMildPressure
    {A : ℝ → WeightedLatticeBanach} (hA : PressureFourierSpacetimeRapid A) :
    SmoothPressureOnNonnegativeTime (physicalMildPressure A) := by
  intro z hz
  change ContDiffWithinAt ℝ ∞ (fun y : ℝ × Space =>
    (∑' m : LatticeMode, physicalSpacetimePressureModeTerm A m y).re)
      nonnegativeSpacetime z
  have hc := contDiffWithinAt_complexPhysicalPressure hA hz
  have hre : ContDiffWithinAt ℝ ∞
      (fun _ : ℝ × Space => Complex.reCLM) nonnegativeSpacetime z :=
    contDiffWithinAt_const
  simpa using hre.clm_apply hc

theorem spatiallyPeriodicPressure_physicalMildPressure
    (A : ℝ → WeightedLatticeBanach) :
    SpatiallyPeriodicPressure (physicalMildPressure A) := by
  intro t _ht x i
  unfold physicalMildPressure physicalSpacetimePressureModeTerm
  congr 1
  apply tsum_congr
  intro m
  rw [latticeCharacter_add_basisVector]

end Navier.Analysis.PeriodicMildClassicalRealization
