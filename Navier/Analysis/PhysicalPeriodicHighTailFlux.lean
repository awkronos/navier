import Navier.Analysis.PhysicalPeriodicEnergyEvolution

/-!
# Quantitative physical high-frequency energy flux

The total nonlinear energy transfer vanishes, but a high-frequency portion
can exchange energy with its complement.  This file bounds that transfer by
the moving high tail of the actual completed critical carrier.  Low--low
interactions are excluded by the exact lattice triangle inequality already
proved in `PeriodicGlobalCriticalControl`.

The resulting estimate is dynamic input for a tail evolution argument.  Its
coefficient contains the current critical carrier norm; removing that factor
uniformly for arbitrary large data is the remaining global-control problem.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicHighTailFlux

open Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PeriodicGlobalCriticalControl
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution

/-- Real projected nonlinear energy transfer into output modes at or above
the cutoff `N`. -/
def projectedHighTriadEnergy (N : ℝ) (u : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  if N ≤ latticeModeSize (ij.1 + ij.2) then
    projectedPhysicalTriadEnergy u ij.1 ij.2
  else 0

/-- The high-output energy term is controlled by the checked high-output pair
mass, with one global coefficient norm from the energy test function. -/
theorem abs_projectedHighTriadEnergy_le
    (N : ℝ) (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u)
    (ij : LatticeMode × LatticeMode) :
    |projectedHighTriadEnergy N u ij| ≤
      ‖u‖ * highOutputPairMass N u u ij := by
  unfold projectedHighTriadEnergy highOutputPairMass
  split_ifs with hout
  · simpa [projectedTriadEnergyMajorant, mul_assoc] using
      abs_projectedPhysicalTriadEnergy_le_majorant u hdiv ij.1 ij.2
  · simp

/-- Absolute summability of the high-frequency energy flux follows from the
actual completed carrier, without an extra moment assumption. -/
theorem summable_projectedHighTriadEnergy
    (N : ℝ) (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u) :
    Summable (projectedHighTriadEnergy N u) := by
  have hmajor : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u‖ * highOutputPairMass N u u ij :=
    (summable_highOutputPairMass N u u).mul_left ‖u‖
  exact hmajor.of_norm_bounded (abs_projectedHighTriadEnergy_le N u hdiv)

/-- The completed nonlinear energy flux in the repository's raw
`A = -2π i û` normalization into the high-output region. -/
def rawHighFrequencyEnergyFlux
    (N : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  ∑' ij : LatticeMode × LatticeMode, projectedHighTriadEnergy N u ij

/-- **Moving-tail flux inequality.**  The magnitude of the actual projected
nonlinear energy transfer into `|k| ≥ N` is at most twice the current carrier
tail above `N/2`, times the square of the current carrier norm. -/
theorem abs_rawHighFrequencyEnergyFlux_le_movingTail
    (N : ℝ) (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u) :
    |rawHighFrequencyEnergyFlux N u| ≤
      2 * ‖u‖ ^ 2 * carrierHighTail (N / 2) u := by
  have hflux := summable_projectedHighTriadEnergy N u hdiv
  have hmajor : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u‖ * highOutputPairMass N u u ij :=
    (summable_highOutputPairMass N u u).mul_left ‖u‖
  have hpoint := abs_projectedHighTriadEnergy_le N u hdiv
  have hpairs := tsum_highOutputPairMass_le_highInputTails N u u
  unfold rawHighFrequencyEnergyFlux
  calc
    |∑' ij : LatticeMode × LatticeMode, projectedHighTriadEnergy N u ij| =
        ‖∑' ij : LatticeMode × LatticeMode,
          projectedHighTriadEnergy N u ij‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' ij : LatticeMode × LatticeMode,
        ‖projectedHighTriadEnergy N u ij‖ :=
      norm_tsum_le_tsum_norm hflux.norm
    _ ≤ ∑' ij : LatticeMode × LatticeMode,
        ‖u‖ * highOutputPairMass N u u ij :=
      hflux.norm.tsum_le_tsum (fun ij => by
        rw [Real.norm_eq_abs]
        exact hpoint ij) hmajor
    _ = ‖u‖ *
        (∑' ij : LatticeMode × LatticeMode, highOutputPairMass N u u ij) :=
      tsum_mul_left
    _ ≤ ‖u‖ *
        (carrierHighTail (N / 2) u * ‖u‖ +
          ‖u‖ * carrierHighTail (N / 2) u) :=
      mul_le_mul_of_nonneg_left hpairs (norm_nonneg _)
    _ = 2 * ‖u‖ ^ 2 * carrierHighTail (N / 2) u := by ring

/-- Along any physical divergence-free carrier path, the same estimate holds
pointwise with the current norm and current tail. -/
theorem abs_rawHighFrequencyEnergyFlux_path_le
    (N : ℝ) (u : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ t, LatticeDivergenceFree (u t)) (t : ℝ) :
    |rawHighFrequencyEnergyFlux N (u t)| ≤
      2 * ‖u t‖ ^ 2 * carrierHighTail (N / 2) (u t) :=
  abs_rawHighFrequencyEnergyFlux_le_movingTail N (u t) (hdiv t)

/-! ## Viscous coercivity on the same moving high region -/

/-- Modal energy density in decoded raw `A = -2π i û` coordinates.  It is
`(2π)²` times the physical Fourier modal energy density before any conventional
factor `1/2`. -/
def rawSpectralEnergyDensity
    (u : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  weightedAmplitude u k ^ 2

/-- Viscous density in decoded raw coordinates, before multiplication by the
raw heat coefficient.  It has the same `(2π)²` amplitude scaling. -/
def rawSpectralDissipationDensity
    (u : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  latticeModeSize k ^ 2 * weightedAmplitude u k ^ 2

theorem summable_rawSpectralEnergyDensity
    (u : WeightedLatticeBanach) :
    Summable (rawSpectralEnergyDensity u) := by
  have hbase : Summable fun k : LatticeMode => ‖u‖ * ‖u k‖ :=
    (summable_norm_weighted u).mul_left ‖u‖
  apply hbase.of_nonneg_of_le
  · intro k
    exact sq_nonneg _
  · intro k
    have ha : weightedAmplitude u k ≤ ‖u k‖ := by
      exact complexEuclideanNorm_weightedLatticeCoefficient_le_eval u k
    have hk : ‖u k‖ ≤ ‖u‖ := norm_weightedLattice_eval_le u k
    have ha0 := weightedAmplitude_nonneg u k
    have hk0 := norm_nonneg (u k)
    change weightedAmplitude u k ^ 2 ≤ ‖u‖ * ‖u k‖
    nlinarith

theorem summable_rawSpectralDissipationDensity
    (u : WeightedLatticeBanach) :
    Summable (rawSpectralDissipationDensity u) := by
  have hbase : Summable fun k : LatticeMode => ‖u‖ * ‖u k‖ :=
    (summable_norm_weighted u).mul_left ‖u‖
  apply hbase.of_nonneg_of_le
  · intro k
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro k
    have hweighted : latticeModeSize k * weightedAmplitude u k ≤ ‖u k‖ := by
      simpa [latticeModeSize, weightedAmplitude] using
        frequency_mul_coefficient_le_eval u k
    have hk : ‖u k‖ ≤ ‖u‖ := norm_weightedLattice_eval_le u k
    have hw0 : 0 ≤ latticeModeSize k * weightedAmplitude u k :=
      mul_nonneg (latticeModeSize_nonneg k) (weightedAmplitude_nonneg u k)
    have hk0 := norm_nonneg (u k)
    change latticeModeSize k ^ 2 * weightedAmplitude u k ^ 2 ≤
      ‖u‖ * ‖u k‖
    have hsquare : (latticeModeSize k * weightedAmplitude u k) ^ 2 ≤
        ‖u k‖ ^ 2 := by nlinarith
    have hknorm : ‖u k‖ ^ 2 ≤ ‖u‖ * ‖u k‖ := by nlinarith
    nlinarith

/-- Raw-normalized energy contained in decoded modes above the cutoff. -/
def rawHighSpectralEnergy
    (N : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode,
    if N ≤ latticeModeSize k then rawSpectralEnergyDensity u k else 0

/-- Raw-normalized dissipation contained in decoded modes above the cutoff. -/
def rawHighSpectralDissipation
    (N : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode,
    if N ≤ latticeModeSize k then rawSpectralDissipationDensity u k else 0

theorem summable_rawHighSpectralEnergy
    (N : ℝ) (u : WeightedLatticeBanach) :
    Summable fun k : LatticeMode =>
      if N ≤ latticeModeSize k then rawSpectralEnergyDensity u k else 0 := by
  exact (summable_rawSpectralEnergyDensity u).of_nonneg_of_le
    (fun k => by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl)
    (fun k => by
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _)

theorem summable_rawHighSpectralDissipation
    (N : ℝ) (u : WeightedLatticeBanach) :
    Summable fun k : LatticeMode =>
      if N ≤ latticeModeSize k then
        rawSpectralDissipationDensity u k else 0 := by
  exact (summable_rawSpectralDissipationDensity u).of_nonneg_of_le
    (fun k => by
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      · exact le_rfl)
    (fun k => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Viscosity is coercive by `N²` on the high region. -/
theorem cutoff_sq_mul_highEnergy_le_highDissipation
    (N : ℝ) (hN : 0 ≤ N) (u : WeightedLatticeBanach) :
    N ^ 2 * rawHighSpectralEnergy N u ≤
      rawHighSpectralDissipation N u := by
  let e : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralEnergyDensity u k else 0
  let d : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralDissipationDensity u k else 0
  have he : Summable e := summable_rawHighSpectralEnergy N u
  have hd : Summable d := summable_rawHighSpectralDissipation N u
  have hpoint : ∀ k, N ^ 2 * e k ≤ d k := by
    intro k
    dsimp [e, d]
    split_ifs with hk
    · unfold rawSpectralEnergyDensity rawSpectralDissipationDensity
      have hs := latticeModeSize_nonneg k
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ hN hs).2 hk) (sq_nonneg _)
    · simp
  unfold rawHighSpectralEnergy rawHighSpectralDissipation
  rw [← tsum_mul_left]
  exact (he.mul_left (N ^ 2)).tsum_le_tsum hpoint hd

/-- Algebraic high-frequency generator inequality.  Viscous damping absorbs
`N²` times the high energy, while all nonlinear leakage is reduced to the
moving critical tail. -/
theorem highEnergyGenerator_le_damping_add_movingTail
    (μ N : ℝ) (hμ : 0 ≤ μ) (hN : 0 ≤ N)
    (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u) :
    2 * rawHighFrequencyEnergyFlux N u -
        2 * μ * rawHighSpectralDissipation N u ≤
      -(2 * μ * N ^ 2) * rawHighSpectralEnergy N u +
        4 * ‖u‖ ^ 2 * carrierHighTail (N / 2) u := by
  have hflux := abs_rawHighFrequencyEnergyFlux_le_movingTail N u hdiv
  have hflux' : rawHighFrequencyEnergyFlux N u ≤
      2 * ‖u‖ ^ 2 * carrierHighTail (N / 2) u :=
    (le_abs_self _).trans hflux
  have hdamp := cutoff_sq_mul_highEnergy_le_highDissipation N hN u
  have hfactor : 0 ≤ 2 * μ := mul_nonneg (by norm_num) hμ
  nlinarith

end Navier.Analysis.PhysicalPeriodicHighTailFlux
