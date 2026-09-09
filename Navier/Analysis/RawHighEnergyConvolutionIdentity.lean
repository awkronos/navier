import Navier.Analysis.PhysicalPeriodicHighTailFlux
import Navier.Analysis.CriticalMildModeDifferentiation

/-!
# Raw high-energy forcing as the exact triad flux

The differentiated mild equation uses `projectedModeForcing`, formed from the
literal completed convolution one output mode at a time.  The high-tail energy
estimate uses a double series of projected triads.  This file proves that the
two expressions are identical.  Absolute convergence is derived from the
weighted carrier, and the final passage uses the repository's exact
output-fiber equivalence rather than a formal rearrangement of an unchecked
series.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.RawHighEnergyConvolutionIdentity

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighTailFlux

/-- Real Hermitian pairing with one decoded raw coefficient, as a continuous
real-linear functional on a convolution fiber. -/
def rawEnergyPairingCLM (u : WeightedLatticeBanach) (k : LatticeMode) :
    ComplexE3 →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((innerSL ℂ
      (complexEuclideanPoint (weightedLatticeCoefficient u k))).restrictScalars ℝ)

@[simp] theorem rawEnergyPairingCLM_apply
    (u : WeightedLatticeBanach) (k : LatticeMode) (z : ComplexE3) :
    rawEnergyPairingCLM u k z =
      (inner ℂ (complexEuclideanPoint (weightedLatticeCoefficient u k)) z).re :=
  rfl

/-- On one literal convolution summand, the energy functional is the
projected triad energy when the pair belongs to the output fiber, and zero
otherwise. -/
theorem rawEnergyPairingCLM_latticeSpectralTerm
    (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u)
    (k : LatticeMode) (ij : LatticeMode × LatticeMode) :
    rawEnergyPairingCLM u k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient u) ij) =
      if ij.1 + ij.2 = k then
        projectedPhysicalTriadEnergy u ij.1 ij.2
      else 0 := by
  by_cases hij : ij.1 + ij.2 = k
  · subst k
    simp only [latticeSpectralTerm, ↓reduceIte, rawEnergyPairingCLM_apply]
    rw [projectedPhysicalTriadEnergy_eq u hdiv]
    rfl
  · simp [latticeSpectralTerm, hij]

/-- At one output mode, pairing the actual projected forcing against the raw
coefficient equals the absolutely convergent energy sum over its exact output
fiber. -/
theorem re_inner_projectedModeForcing_eq_fiber
    (A : ℝ → WeightedLatticeBanach) (hdiv : ∀ t, LatticeDivergenceFree (A t))
    (t : ℝ) (k : LatticeMode) :
    (inner ℂ
      (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
      (complexEuclideanPoint (projectedModeForcing A k t))).re =
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        projectedPhysicalTriadEnergy (A t) ij.1.1 ij.1.2 := by
  let u := A t
  have hterms : Summable
      (latticeSpectralTerm k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient u)) :=
    summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient u))
  have hmap := (rawEnergyPairingCLM u k).map_tsum hterms
  have hmode :
      (inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient u k))
        (complexEuclideanPoint (projectedModeForcing A k t))).re =
        rawEnergyPairingCLM u k
          (weightedLatticeSpectralConvolution k u u) := by
    unfold projectedModeForcing spectralOutputCoefficient
    rw [inner_output_complexLeray_eq u (hdiv t) k]
    rfl
  rw [hmode]
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [hmap]
  rw [show (fun ij : LatticeMode × LatticeMode =>
      rawEnergyPairingCLM u k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient u) ij)) =
      (fun ij => if ij.1 + ij.2 = k then
        projectedPhysicalTriadEnergy u ij.1 ij.2 else 0) by
    funext ij
    exact rawEnergyPairingCLM_latticeSpectralTerm u (hdiv t) k ij]
  rw [tsum_subtype (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
    (fun ij : LatticeMode × LatticeMode =>
      projectedPhysicalTriadEnergy u ij.1 ij.2)]
  apply tsum_congr
  intro ij
  by_cases hij : ij.1 + ij.2 = k
  · rw [if_pos hij]
    simp [Set.indicator, latticeOutputMode, hij]
  · rw [if_neg hij]
    simp [Set.indicator, latticeOutputMode, hij]

/-- Summability of the output-mode energy pairing follows from the single
absolutely convergent double triad family. -/
theorem summable_re_inner_projectedModeForcing
    (A : ℝ → WeightedLatticeBanach) (hdiv : ∀ t, LatticeDivergenceFree (A t))
    (t : ℝ) :
    Summable fun k : LatticeMode =>
      (inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
        (complexEuclideanPoint (projectedModeForcing A k t))).re := by
  let u := A t
  have hp := summable_projectedPhysicalTriadEnergy u (hdiv t)
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      projectedPhysicalTriadEnergy u x.2.1.1 x.2.1.2) := by
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
  have hfiber := hsigma.sigma
  simpa only [re_inner_projectedModeForcing_eq_fiber A hdiv t] using hfiber

/-- Summing the actual modewise projected forcing over high outputs is exactly
the raw-normalized high-frequency triad flux. -/
theorem tsum_re_inner_projectedModeForcing_high_eq_rawFlux
    (N : ℝ) (A : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ t, LatticeDivergenceFree (A t)) (t : ℝ) :
    (∑' k : LatticeMode,
      if N ≤ latticeModeSize k then
        (inner ℂ
          (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
          (complexEuclideanPoint (projectedModeForcing A k t))).re
      else 0) = rawHighFrequencyEnergyFlux N (A t) := by
  let u := A t
  let F : (Σ k : LatticeMode,
      latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) → ℝ := fun x =>
    if N ≤ latticeModeSize x.1 then
      projectedPhysicalTriadEnergy u x.2.1.1 x.2.1.2
    else 0
  have hp : Summable (projectedHighTriadEnergy N u) :=
    summable_projectedHighTriadEnergy N u (hdiv t)
  have hFEq : F = fun x =>
      projectedHighTriadEnergy N u (latticeOutputFiberSigmaEquiv x) := by
    funext x
    have hx := x.2.2
    change latticeOutputMode x.2.1 = x.1 at hx
    change (if N ≤ latticeModeSize x.1 then
        projectedPhysicalTriadEnergy u x.2.1.1 x.2.1.2 else 0) =
      (if N ≤ latticeModeSize (x.2.1.1 + x.2.1.2) then
        projectedPhysicalTriadEnergy u x.2.1.1 x.2.1.2 else 0)
    change x.2.1.1 + x.2.1.2 = x.1 at hx
    rw [hx]
  have hF : Summable F := by
    rw [hFEq]
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
  have hsigma := hF.tsum_sigma
  have hreindex := latticeOutputFiberSigmaEquiv.tsum_eq
    (projectedHighTriadEnergy N u)
  unfold rawHighFrequencyEnergyFlux
  rw [← hreindex, ← hFEq, hsigma]
  apply tsum_congr
  intro k
  by_cases hk : N ≤ latticeModeSize k
  · rw [if_pos hk]
    simp only [F, hk, if_true]
    exact re_inner_projectedModeForcing_eq_fiber A hdiv t k
  · rw [if_neg hk]
    simp [F, hk]

end Navier.Analysis.RawHighEnergyConvolutionIdentity
