import Navier.Analysis.PhysicalPeriodicTailMomentControl

/-!
# Frequency-local form of physical periodic energy cancellation

Unweighted physical energy transfer cancels exactly after exchanging the two
transported members of a zero-sum triad.  A frequency weight breaks that
cancellation only through the difference of the two output weights.  The
reverse triangle inequality bounds this commutator by the size of the fixed
advecting mode.

This is the favorable frequency-local cancellation available to a weighted
energy argument.  Its countable sum is controlled by one half-generator
moment and two completed-carrier factors.  Thus the estimate identifies the
same higher moment that appears in the moving-tail route; energy cancellation
alone does not remove it.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicWeightedFluxCommutator

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution

/-- The homogeneous lattice size is even. -/
theorem latticeModeSize_neg (k : LatticeMode) :
    latticeModeSize (-k) = latticeModeSize k := by
  unfold latticeModeSize
  have hfreq : complexFrequency (latticeFrequency (-k)) =
      -complexFrequency (latticeFrequency k) := by
    ext a
    fin_cases a <;>
      simp [latticeFrequency, complexFrequency, complexEuclideanPoint,
        complexOfReal, complexOfParts]
  rw [hfreq, norm_neg]

theorem complexFrequency_latticeFrequency_neg (k : LatticeMode) :
    complexFrequency (latticeFrequency (-k)) =
      -complexFrequency (latticeFrequency k) := by
  ext a
  fin_cases a <;>
    simp [latticeFrequency, complexFrequency, complexEuclideanPoint,
      complexOfReal, complexOfParts]

/-- In a zero-sum triad, the two output frequencies paired by physical energy
cancellation differ in norm by at most the fixed advecting frequency. -/
theorem abs_output_weight_gap_le_advecting_size
    (i j l : LatticeMode) (hijl : i + j + l = 0) :
    |latticeModeWeight (i + j) - latticeModeWeight (i + l)| ≤
      latticeModeSize i := by
  have hij : i + j = -l := eq_neg_of_add_eq_zero_left hijl
  have hilj : i + l + j = 0 := by
    calc
      i + l + j = i + j + l := by ac_rfl
      _ = 0 := hijl
  have hil : i + l = -j := eq_neg_of_add_eq_zero_left hilj
  have hli : l + j = -i := by
    apply eq_neg_of_add_eq_zero_left
    calc
      l + j + i = i + j + l := by ac_rfl
      _ = 0 := hijl
  rw [hij, hil, latticeModeWeight_eq_one_add_size,
    latticeModeWeight_eq_one_add_size, latticeModeSize_neg,
    latticeModeSize_neg]
  have hgap := abs_norm_sub_norm_le
    (complexFrequency (latticeFrequency l))
    (complexFrequency (latticeFrequency (-j)))
  have hdiff : complexFrequency (latticeFrequency l) -
      complexFrequency (latticeFrequency (-j)) =
      complexFrequency (latticeFrequency (-i)) := by
    have hadd := complexFrequency_latticeFrequency_add l j
    rw [hli] at hadd
    rw [complexFrequency_latticeFrequency_neg, sub_neg_eq_add]
    exact hadd.symm
  rw [hdiff] at hgap
  change |latticeModeSize l - latticeModeSize (-j)| ≤ latticeModeSize (-i) at hgap
  rw [latticeModeSize_neg j, latticeModeSize_neg i] at hgap
  simpa only [add_sub_add_left_eq_sub] using hgap

/-- One pair of output-weighted projected energy transfers, using the exact
physical cancellation partner. -/
def weightedProjectedTriadPair
    (u : WeightedLatticeBanach) (i j l : LatticeMode) : ℝ :=
  latticeModeWeight (i + j) * projectedPhysicalTriadEnergy u i j +
    latticeModeWeight (i + l) * projectedPhysicalTriadEnergy u i l

/-- Exact commutator identity: weighting leaves only the output-weight gap
times either member of the cancelling pair. -/
theorem weightedProjectedTriadPair_eq_weightGap
    (u : WeightedLatticeBanach) (hphysical : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u)
    (i j l : LatticeMode) (hijl : i + j + l = 0) :
    weightedProjectedTriadPair u i j l =
      (latticeModeWeight (i + j) - latticeModeWeight (i + l)) *
        projectedPhysicalTriadEnergy u i j := by
  have hcancel := projectedPhysicalTriadEnergy_pair_cancel
    u hphysical hdiv i j l hijl
  have heq : projectedPhysicalTriadEnergy u i l =
      -projectedPhysicalTriadEnergy u i j := by linarith
  unfold weightedProjectedTriadPair
  rw [heq]
  ring

/-- Quantitative frequency-local commutator estimate.  Compared with the
uncancelled cubic majorant, the only derivative loss is the advecting-mode
size forced by the reverse triangle inequality. -/
theorem abs_weightedProjectedTriadPair_le
    (u : WeightedLatticeBanach) (hphysical : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u)
    (i j l : LatticeMode) (hijl : i + j + l = 0) :
    |weightedProjectedTriadPair u i j l| ≤
      latticeModeSize i * projectedTriadEnergyMajorant u (i, j) := by
  rw [weightedProjectedTriadPair_eq_weightGap u hphysical hdiv i j l hijl,
    abs_mul]
  exact mul_le_mul
    (abs_output_weight_gap_le_advecting_size i j l hijl)
    (abs_projectedPhysicalTriadEnergy_le_majorant u hdiv i j)
    (abs_nonneg _) (latticeModeSize_nonneg i)

/-- The actual commutator family indexed by all ordered input pairs. -/
def weightedTriadCommutator
    (u : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) : ℝ :=
  weightedProjectedTriadPair u ij.1 ij.2 (-(ij.1 + ij.2))

/-- The countable weighted commutator is absolutely summable on the
half-generator domain. -/
theorem summable_weightedTriadCommutator
    (u : WeightedLatticeBanach) (hphysical : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u)
    (hhalf : Summable fun i : LatticeMode => latticeModeSize i * ‖u i‖) :
    Summable (weightedTriadCommutator u) := by
  have hu : Summable fun j : LatticeMode => ‖u j‖ := by
    simpa using u.2.summable
  have hp : Summable fun ij : LatticeMode × LatticeMode =>
      (latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖ :=
    hhalf.mul_of_nonneg hu
      (fun i => mul_nonneg (latticeModeSize_nonneg i) (norm_nonneg _))
      (fun j => norm_nonneg _)
  have hmajor : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u‖ * ((latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖) :=
    hp.mul_left ‖u‖
  apply hmajor.of_norm_bounded
  intro ij
  rw [Real.norm_eq_abs]
  have hzero : ij.1 + ij.2 + (-(ij.1 + ij.2)) = 0 := by simp
  have h := abs_weightedProjectedTriadPair_le
    u hphysical hdiv ij.1 ij.2 (-(ij.1 + ij.2)) hzero
  calc
    |weightedTriadCommutator u ij| ≤
        latticeModeSize ij.1 * projectedTriadEnergyMajorant u (ij.1, ij.2) := h
    _ = ‖u‖ * ((latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖) := by
      unfold projectedTriadEnergyMajorant
      ring

/-- The full absolutely convergent commutator is bounded by two carrier
factors and one half-generator moment. -/
theorem abs_tsum_weightedTriadCommutator_le
    (u : WeightedLatticeBanach) (hphysical : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u)
    (hhalf : Summable fun i : LatticeMode => latticeModeSize i * ‖u i‖) :
    |∑' ij : LatticeMode × LatticeMode, weightedTriadCommutator u ij| ≤
      ‖u‖ ^ 2 * heatHalfGeneratorMoment u := by
  have hs := summable_weightedTriadCommutator u hphysical hdiv hhalf
  have hu : Summable fun j : LatticeMode => ‖u j‖ := by
    simpa using u.2.summable
  have hp : Summable fun ij : LatticeMode × LatticeMode =>
      (latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖ :=
    hhalf.mul_of_nonneg hu
      (fun i => mul_nonneg (latticeModeSize_nonneg i) (norm_nonneg _))
      (fun j => norm_nonneg _)
  have hmajor : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u‖ * ((latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖) :=
    hp.mul_left ‖u‖
  calc
    |∑' ij : LatticeMode × LatticeMode, weightedTriadCommutator u ij| =
        ‖∑' ij : LatticeMode × LatticeMode, weightedTriadCommutator u ij‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' ij : LatticeMode × LatticeMode,
        ‖weightedTriadCommutator u ij‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ij : LatticeMode × LatticeMode,
        ‖u‖ * ((latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖) := by
      exact hs.norm.tsum_le_tsum (fun ij => by
        rw [Real.norm_eq_abs]
        have hzero : ij.1 + ij.2 + (-(ij.1 + ij.2)) = 0 := by simp
        have h := abs_weightedProjectedTriadPair_le
          u hphysical hdiv ij.1 ij.2 (-(ij.1 + ij.2)) hzero
        calc
          |weightedTriadCommutator u ij| ≤
              latticeModeSize ij.1 *
                projectedTriadEnergyMajorant u (ij.1, ij.2) := h
          _ = ‖u‖ *
              ((latticeModeSize ij.1 * ‖u ij.1‖) * ‖u ij.2‖) := by
            unfold projectedTriadEnergyMajorant
            ring) hmajor
    _ = ‖u‖ *
        ((∑' i : LatticeMode, latticeModeSize i * ‖u i‖) *
          ∑' j : LatticeMode, ‖u j‖) := by
      rw [tsum_mul_left, ← hhalf.tsum_mul_tsum hu hp]
    _ = ‖u‖ ^ 2 * heatHalfGeneratorMoment u := by
      rw [← norm_eq_tsum_norm u]
      unfold heatHalfGeneratorMoment latticeModeSize
      ring

end Navier.Analysis.PhysicalPeriodicWeightedFluxCommutator
