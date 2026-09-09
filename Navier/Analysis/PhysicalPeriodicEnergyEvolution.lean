import Navier.Analysis.PhysicalPeriodicGlobalControl

/-!
# Summed physical periodic energy cancellation

This file lifts the checked local triad cancellation to the actual countable
lattice.  Absolute summability is derived from the completed weighted `ℓ¹`
carrier itself.  Reindexing by the exact triad involution then proves that the
entire Leray-projected nonlinear contribution to the real energy balance is
zero.

The result supplies the nonlinear cancellation needed by an energy evolution
argument.  It does not identify weighted `ℓ²` energy with the critical `ℓ¹`
terminal quantity; a horizon-uniform high-frequency estimate is still needed
for that passage.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicEnergyEvolution

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.PhysicalPeriodicGlobalControl

/-- Every decoded Fourier coefficient is bounded by its weighted `ℓ¹`
coordinate. -/
theorem complexEuclideanNorm_weightedLatticeCoefficient_le_eval
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    complexEuclideanNorm (weightedLatticeCoefficient u m) ≤ ‖u m‖ := by
  have hw := one_le_latticeModeWeight m
  have hn : 0 ≤ complexEuclideanNorm (weightedLatticeCoefficient u m) :=
    norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hw hn
  rw [one_mul] at hmul
  rw [← latticeWeightedAmplitude_coefficient u m]
  exact hmul

/-- The derivative frequency times a decoded coefficient is bounded by the
same weighted `ℓ¹` coordinate. -/
theorem frequency_mul_coefficient_le_eval
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    ‖complexFrequency (latticeFrequency m)‖ *
        complexEuclideanNorm (weightedLatticeCoefficient u m) ≤ ‖u m‖ := by
  have hf : ‖complexFrequency (latticeFrequency m)‖ ≤ latticeModeWeight m := by
    unfold latticeModeWeight
    linarith [norm_nonneg (complexFrequency (latticeFrequency m))]
  have hn : 0 ≤ complexEuclideanNorm (weightedLatticeCoefficient u m) :=
    norm_nonneg _
  calc
    ‖complexFrequency (latticeFrequency m)‖ *
        complexEuclideanNorm (weightedLatticeCoefficient u m) ≤
      latticeModeWeight m *
        complexEuclideanNorm (weightedLatticeCoefficient u m) :=
          mul_le_mul_of_nonneg_right hf hn
    _ = ‖u m‖ := latticeWeightedAmplitude_coefficient u m

/-- A product majorant for the real energy transfer of one ordered triad. -/
def projectedTriadEnergyMajorant
    (u : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) : ℝ :=
  ‖u‖ * ‖u ij.1‖ * ‖u ij.2‖

/-- The actual projected triad energy is bounded by the product majorant. -/
theorem abs_projectedPhysicalTriadEnergy_le_majorant
    (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u)
    (i j : LatticeMode) :
    |projectedPhysicalTriadEnergy u i j| ≤
      projectedTriadEnergyMajorant u (i, j) := by
  rw [projectedPhysicalTriadEnergy_eq u hdiv i j]
  unfold physicalTriadEnergy projectedTriadEnergyMajorant
  have hout : complexEuclideanNorm
      (weightedLatticeCoefficient u (i + j)) ≤ ‖u‖ :=
    (complexEuclideanNorm_weightedLatticeCoefficient_le_eval u (i + j)).trans
      (norm_weightedLattice_eval_le u (i + j))
  have hi := complexEuclideanNorm_weightedLatticeCoefficient_le_eval u i
  have hj := frequency_mul_coefficient_le_eval u j
  calc
    |(inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient u (i + j)))
        (complexEuclideanPoint
          (CriticalMildDuhamel.spectralTransport (latticeFrequency j)
            (weightedLatticeCoefficient u i)
            (weightedLatticeCoefficient u j)))).re| ≤
      ‖inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient u (i + j)))
        (complexEuclideanPoint
          (CriticalMildDuhamel.spectralTransport (latticeFrequency j)
            (weightedLatticeCoefficient u i)
            (weightedLatticeCoefficient u j)))‖ := Complex.abs_re_le_norm _
    _ ≤ complexEuclideanNorm (weightedLatticeCoefficient u (i + j)) *
        complexEuclideanNorm
          (CriticalMildDuhamel.spectralTransport (latticeFrequency j)
            (weightedLatticeCoefficient u i)
            (weightedLatticeCoefficient u j)) := norm_inner_le_norm _ _
    _ ≤ complexEuclideanNorm (weightedLatticeCoefficient u (i + j)) *
        (‖complexFrequency (latticeFrequency j)‖ *
          complexEuclideanNorm (weightedLatticeCoefficient u i) *
          complexEuclideanNorm (weightedLatticeCoefficient u j)) := by
      exact mul_le_mul_of_nonneg_left
        (CriticalMildDuhamel.complexEuclideanNorm_spectralTransport_le
          (latticeFrequency j) (weightedLatticeCoefficient u i)
            (weightedLatticeCoefficient u j)) (norm_nonneg _)
    _ ≤ ‖u‖ * (‖u i‖ * ‖u j‖) := by
      have hmiddle : ‖complexFrequency (latticeFrequency j)‖ *
            complexEuclideanNorm (weightedLatticeCoefficient u i) *
            complexEuclideanNorm (weightedLatticeCoefficient u j) ≤
          ‖u i‖ * ‖u j‖ := by
        calc
          ‖complexFrequency (latticeFrequency j)‖ *
                complexEuclideanNorm (weightedLatticeCoefficient u i) *
                complexEuclideanNorm (weightedLatticeCoefficient u j) =
              complexEuclideanNorm (weightedLatticeCoefficient u i) *
                (‖complexFrequency (latticeFrequency j)‖ *
                  complexEuclideanNorm (weightedLatticeCoefficient u j)) := by ring
          _ ≤ ‖u i‖ *
                (‖complexFrequency (latticeFrequency j)‖ *
                  complexEuclideanNorm (weightedLatticeCoefficient u j)) :=
            mul_le_mul_of_nonneg_right hi
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ ‖u i‖ * ‖u j‖ :=
            mul_le_mul_of_nonneg_left hj (norm_nonneg _)
      calc
        complexEuclideanNorm (weightedLatticeCoefficient u (i + j)) *
            (‖complexFrequency (latticeFrequency j)‖ *
              complexEuclideanNorm (weightedLatticeCoefficient u i) *
              complexEuclideanNorm (weightedLatticeCoefficient u j)) ≤
          ‖u‖ *
            (‖complexFrequency (latticeFrequency j)‖ *
              complexEuclideanNorm (weightedLatticeCoefficient u i) *
              complexEuclideanNorm (weightedLatticeCoefficient u j)) :=
            mul_le_mul_of_nonneg_right hout
              (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (norm_nonneg _))
        _ ≤ ‖u‖ * (‖u i‖ * ‖u j‖) :=
          mul_le_mul_of_nonneg_left hmiddle (norm_nonneg _)
    _ = ‖u‖ * ‖u i‖ * ‖u j‖ := by ring

/-- The cubic product majorant is summable on all ordered lattice pairs. -/
theorem summable_projectedTriadEnergyMajorant
    (u : WeightedLatticeBanach) :
    Summable (projectedTriadEnergyMajorant u) := by
  have hu : Summable fun m : LatticeMode => ‖u m‖ := by
    simpa using u.2.summable
  have hp : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u ij.1‖ * ‖u ij.2‖ :=
    hu.mul_of_nonneg hu (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  change Summable fun ij : LatticeMode × LatticeMode =>
    ‖u‖ * ‖u ij.1‖ * ‖u ij.2‖
  have heq : (fun ij : LatticeMode × LatticeMode =>
      ‖u‖ * ‖u ij.1‖ * ‖u ij.2‖) =
      (fun ij => ‖u‖ * (‖u ij.1‖ * ‖u ij.2‖)) := by
    funext ij
    ring
  rw [heq]
  exact hp.mul_left ‖u‖

/-- The actual projected triad-energy family is absolutely summable for every
completed weighted carrier. -/
theorem summable_projectedPhysicalTriadEnergy
    (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u) :
    Summable fun ij : LatticeMode × LatticeMode =>
      projectedPhysicalTriadEnergy u ij.1 ij.2 := by
  exact (summable_projectedTriadEnergyMajorant u).of_norm_bounded
    (fun ij => abs_projectedPhysicalTriadEnergy_le_majorant u hdiv ij.1 ij.2)

/-- Involution that fixes the advecting mode and exchanges the transported
mode with the third member of its zero-sum triad. -/
def triadEnergySwap :
    (LatticeMode × LatticeMode) ≃ (LatticeMode × LatticeMode) where
  toFun ij := (ij.1, -(ij.1 + ij.2))
  invFun ij := (ij.1, -(ij.1 + ij.2))
  left_inv ij := by
    rcases ij with ⟨i, j⟩
    apply Prod.ext
    · rfl
    · simp
  right_inv ij := by
    rcases ij with ⟨i, j⟩
    apply Prod.ext
    · rfl
    · simp

/-- The full absolutely convergent real energy contribution of the actual
Leray-projected lattice nonlinearity is zero. -/
theorem tsum_projectedPhysicalTriadEnergy_eq_zero
    (u : WeightedLatticeBanach) (hphysical : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u) :
    (∑' ij : LatticeMode × LatticeMode,
      projectedPhysicalTriadEnergy u ij.1 ij.2) = 0 := by
  let f : LatticeMode × LatticeMode → ℝ := fun ij =>
    projectedPhysicalTriadEnergy u ij.1 ij.2
  have hf : Summable f := summable_projectedPhysicalTriadEnergy u hdiv
  have hswap : Summable fun ij => f (triadEnergySwap ij) := by
    simpa [Function.comp_def] using
      (triadEnergySwap.summable_iff.mpr hf)
  have hpair : ∀ ij, f ij + f (triadEnergySwap ij) = 0 := by
    intro ij
    rcases ij with ⟨i, j⟩
    apply projectedPhysicalTriadEnergy_pair_cancel u hphysical hdiv
      i j (-(i + j))
    simp
  have hzero : (∑' ij, (f ij + f (triadEnergySwap ij))) = 0 := by
    simp_rw [hpair]
    exact tsum_zero
  rw [hf.tsum_add hswap, Equiv.tsum_eq triadEnergySwap f] at hzero
  have : (∑' ij, f ij) = 0 := by linarith
  exact this

end Navier.Analysis.PhysicalPeriodicEnergyEvolution
