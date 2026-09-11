import Navier.Analysis.LeiLinPositiveRestartEnergy

/-!
# Canonical Fourier truncations of the actual critical mild image

The completed critical mild construction already exposes a concrete countable
Fourier carrier.  Its canonical finite-mode approximation is therefore the
partial sum of the carrier's `lp.single` expansion.  This file proves that the
partial sums converge to the actual mild image and have finite graph norm, and
records the sharp uniformity criterion: a uniform graph-moment (or squared
graph-moment) bound exists exactly when the untruncated value is already in the
half-generator domain.

Thus output-mode truncation is a genuine approximation of the existing fixed
point, but it cannot create the missing positive-time `X2` estimate uniformly.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.LeiLinPositiveRestartFourier

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinPositiveRestart

/-- Coordinate evaluation as an additive map, used to push evaluation through
finite carrier sums. -/
def weightedLatticeEvalAddHom (m : LatticeMode) :
    WeightedLatticeBanach →+ ComplexE3 where
  toFun u := u m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The first `n` coordinates of the canonical countable lattice enumeration,
inserted into the actual completed one-weight carrier. -/
def fourierTruncation (n : ℕ) (u : WeightedLatticeBanach) :
    WeightedLatticeBanach :=
  ∑ j ∈ Finset.range n,
    (lp.single 1 (latticeModeEquivNat.symm j)
      (u (latticeModeEquivNat.symm j)) : WeightedLatticeBanach)

/-- Coordinate formula for the canonical truncation. -/
theorem fourierTruncation_apply (n : ℕ) (u : WeightedLatticeBanach)
    (m : LatticeMode) :
    fourierTruncation n u m =
      if latticeModeEquivNat m < n then u m else 0 := by
  classical
  unfold fourierTruncation
  change weightedLatticeEvalAddHom m
    (∑ j ∈ Finset.range n,
      (lp.single 1 (latticeModeEquivNat.symm j)
        (u (latticeModeEquivNat.symm j)) : WeightedLatticeBanach)) = _
  rw [map_sum]
  simp only [weightedLatticeEvalAddHom]
  by_cases hm : latticeModeEquivNat m < n
  · rw [if_pos hm]
    have hmem : latticeModeEquivNat m ∈ Finset.range n := Finset.mem_range.mpr hm
    rw [Finset.sum_eq_single (latticeModeEquivNat m)]
    · rw [Equiv.symm_apply_apply latticeModeEquivNat m]
      exact lp.single_apply_self (E := fun _ => ComplexE3) 1 m (u m)
    · intro b hb hne
      have hsymm : latticeModeEquivNat.symm b ≠ m := by
        intro h
        apply hne
        simpa using congrArg latticeModeEquivNat h
      exact lp.single_apply_ne (E := fun _ => ComplexE3) 1 (latticeModeEquivNat.symm b) (u (latticeModeEquivNat.symm b))
        (Ne.symm hsymm)
    · exact fun h => (h hmem).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j ≠ latticeModeEquivNat m := by
      intro h
      subst j
      exact hm (Finset.mem_range.mp hj)
    have hsymm : latticeModeEquivNat.symm j ≠ m := by
      intro h
      apply hne
      simpa using congrArg latticeModeEquivNat h
    exact lp.single_apply_ne (E := fun _ => ComplexE3) 1 (latticeModeEquivNat.symm j) (u (latticeModeEquivNat.symm j))
      (Ne.symm hsymm)

/-- Every finite Fourier truncation belongs to the half-generator graph
domain. -/
theorem summable_halfGeneratorMoment_fourierTruncation
    (n : ℕ) (u : WeightedLatticeBanach) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖fourierTruncation n u m‖ := by
  classical
  apply summable_of_ne_finset_zero
    (s := (Finset.range n).image latticeModeEquivNat.symm)
  intro m hm
  have hnot : ¬ latticeModeEquivNat m < n := by
    intro hlt
    apply hm
    refine Finset.mem_image.mpr ⟨latticeModeEquivNat m,
      Finset.mem_range.mpr hlt, ?_⟩
    simp
  simp [fourierTruncation_apply, hnot]

/-- Fourier truncation preserves the pointwise Hermitian-transversality
constraint. -/
theorem fourierTruncation_divergenceFree
    (n : ℕ) (u : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    LatticeDivergenceFree (fourierTruncation n u) := by
  intro m
  by_cases hm : latticeModeEquivNat m < n
  · simpa [weightedLatticeCoefficient, fourierTruncation_apply, hm] using hu m
  · have hpoint : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
      ext j
      rfl
    rw [show weightedLatticeCoefficient (fourierTruncation n u) m =
        (0 : ComplexSpace) by
          simp [weightedLatticeCoefficient, fourierTruncation_apply, hm],
      hpoint, inner_zero_right]

/-- Output-mode projection is contractive in the completed critical carrier,
so the canonical approximants remain in every fixed-point radius ball that
contains the actual value. -/
theorem norm_fourierTruncation_le (n : ℕ) (u : WeightedLatticeBanach) :
    ‖fourierTruncation n u‖ ≤ ‖u‖ := by
  have htrunc : Summable fun m : LatticeMode => ‖fourierTruncation n u m‖ := by
    simpa using (fourierTruncation n u).2.summable
  have hu : Summable fun m : LatticeMode => ‖u m‖ := by
    simpa using u.2.summable
  rw [show ‖fourierTruncation n u‖ =
      ∑' m : LatticeMode, ‖fourierTruncation n u m‖ by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp [ENNReal.toReal_one],
    show ‖u‖ = ∑' m : LatticeMode, ‖u m‖ by
      rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
      simp [ENNReal.toReal_one]]
  apply htrunc.tsum_le_tsum _ hu
  intro m
  rw [fourierTruncation_apply]
  split_ifs
  · exact le_rfl
  · simp

/-- The canonical finite-coordinate partial sums converge in the actual
completed carrier norm. -/
theorem tendsto_fourierTruncation (u : WeightedLatticeBanach) :
    Tendsto (fun n => fourierTruncation n u) atTop (nhds u) := by
  have hsingle := lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤) u
  have hsum : Summable (fun n : ℕ =>
      lp.single (E := fun _ : LatticeMode => ComplexE3) 1
        (latticeModeEquivNat.symm n) (u (latticeModeEquivNat.symm n))) :=
    latticeModeEquivNat.symm.summable_iff.mpr hsingle.summable
  have hsum_eq : (∑' n : ℕ,
      lp.single (E := fun _ : LatticeMode => ComplexE3) 1
        (latticeModeEquivNat.symm n) (u (latticeModeEquivNat.symm n))) = u := by
    calc
      (∑' n : ℕ, lp.single (E := fun _ : LatticeMode => ComplexE3) 1
          (latticeModeEquivNat.symm n) (u (latticeModeEquivNat.symm n))) =
          ∑' m : LatticeMode,
            lp.single (E := fun _ : LatticeMode => ComplexE3) 1 m (u m) :=
        latticeModeEquivNat.symm.tsum_eq
          (fun m : LatticeMode =>
            lp.single (E := fun _ : LatticeMode => ComplexE3) 1 m (u m))
      _ = u := hsingle.tsum_eq
  have hhas := hsum.hasSum_iff.mpr hsum_eq
  simpa [fourierTruncation] using hhas.tendsto_sum_nat

/-- Truncation contracts the half-generator moment whenever the full moment is
summable. -/
theorem heatHalfGeneratorMoment_fourierTruncation_le
    (n : ℕ) (u : WeightedLatticeBanach)
    (hgraph : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) :
    heatHalfGeneratorMoment (fourierTruncation n u) ≤
      heatHalfGeneratorMoment u := by
  unfold heatHalfGeneratorMoment
  apply (summable_halfGeneratorMoment_fourierTruncation n u).tsum_le_tsum _ hgraph
  intro m
  rw [fourierTruncation_apply]
  split_ifs
  · exact le_rfl
  · simpa using mul_nonneg
      (norm_nonneg (complexFrequency (latticeFrequency m))) (norm_nonneg (u m))

/-- **Sharp uniformity criterion for actual Fourier partial sums.** -/
theorem exists_uniform_fourierTruncation_bound_iff_halfGeneratorDomain
    (u : WeightedLatticeBanach) :
    (∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment (fourierTruncation n u) ≤ C) ↔
      Summable (fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) := by
  constructor
  · rintro ⟨C, hC⟩
    exact (summable_halfGeneratorMoment_of_tendsto_of_uniform_bound
      (tendsto_fourierTruncation u)
      (fun n => summable_halfGeneratorMoment_fourierTruncation n u) hC).1
  · intro hgraph
    exact ⟨heatHalfGeneratorMoment u,
      fun n => heatHalfGeneratorMoment_fourierTruncation_le n u hgraph⟩

/-- Squaring the finite-mode graph moment does not improve uniformity: a
uniform square estimate is again exactly full graph-domain membership. -/
theorem exists_uniform_fourierTruncation_sq_bound_iff_halfGeneratorDomain
    (u : WeightedLatticeBanach) :
    (∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment (fourierTruncation n u) ^ 2 ≤ C) ↔
      Summable (fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) := by
  constructor
  · rintro ⟨C, hC⟩
    apply (exists_uniform_fourierTruncation_bound_iff_halfGeneratorDomain u).1
    refine ⟨C + 1, fun n => ?_⟩
    have hM0 := heatHalfGeneratorMoment_nonneg (fourierTruncation n u)
    have hC0 : 0 ≤ C :=
      (sq_nonneg (heatHalfGeneratorMoment (fourierTruncation n u))).trans (hC n)
    by_cases hM1 : heatHalfGeneratorMoment (fourierTruncation n u) ≤ 1
    · linarith
    · have h1M : 1 ≤ heatHalfGeneratorMoment (fourierTruncation n u) :=
        le_of_not_ge hM1
      have hMM : heatHalfGeneratorMoment (fourierTruncation n u) ≤
          heatHalfGeneratorMoment (fourierTruncation n u) ^ 2 := by
        nlinarith [mul_nonneg hM0 (sub_nonneg.mpr h1M)]
      linarith [hMM, hC n]
  · intro hgraph
    refine ⟨heatHalfGeneratorMoment u ^ 2, fun n => ?_⟩
    have hle := heatHalfGeneratorMoment_fourierTruncation_le n u hgraph
    have h0 := heatHalfGeneratorMoment_nonneg (fourierTruncation n u)
    have hu0 := heatHalfGeneratorMoment_nonneg u
    nlinarith

/-- The actual mild image, projected onto the first `n` output modes.  This is
an approximation of the existing completed fixed-point map, not a separately
postulated Galerkin solution. -/
def criticalMildImageFourierTruncation
    (n : ℕ) (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (ht : 0 ≤ t) : WeightedLatticeBanach :=
  fourierTruncation n (criticalMildImage ν hν u₀ u hu t ht)

/-- Finite output-mode projections converge to the literal completed mild
image. -/
theorem tendsto_criticalMildImageFourierTruncation
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n =>
      criticalMildImageFourierTruncation n ν hν u₀ u hu t ht)
      atTop (nhds (criticalMildImage ν hν u₀ u hu t ht)) :=
  tendsto_fourierTruncation _

/-- For a literal fixed-point value, uniform squared graph control of its
canonical finite-mode approximants is equivalent to graph membership of the
actual solution value.  Consequently this approximation does not remove the
positive-time graph premise from the restart consumer. -/
theorem fixedPoint_uniform_fourier_sq_iff_graph
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (ht : 0 ≤ t)
    (hmild : u t = criticalMildImage ν hν u₀ u hu t ht) :
    (∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment
        (criticalMildImageFourierTruncation n ν hν u₀ u hu t ht) ^ 2 ≤ C) ↔
      Summable (fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u t m‖) := by
  rw [hmild]
  exact exists_uniform_fourierTruncation_sq_bound_iff_halfGeneratorDomain _

/-- Checked obstruction to cutoff-uniform nonlinear smoothing: at any fixed
point value outside the graph domain, the squared graph moments of its genuine
Fourier output truncations admit no common bound. -/
theorem fixedPoint_not_exists_uniform_fourier_sq_of_not_graph
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (ht : 0 ≤ t)
    (hmild : u t = criticalMildImage ν hν u₀ u hu t ht)
    (hnot : ¬ Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u t m‖)) :
    ¬ ∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment
        (criticalMildImageFourierTruncation n ν hν u₀ u hu t ht) ^ 2 ≤ C := by
  intro hbound
  exact hnot ((fixedPoint_uniform_fourier_sq_iff_graph
    ν hν u₀ u hu t ht hmild).1 hbound)

end Navier.Analysis.LeiLinPositiveRestartFourier

#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.tendsto_fourierTruncation
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.summable_halfGeneratorMoment_fourierTruncation
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.fourierTruncation_divergenceFree
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.norm_fourierTruncation_le
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.exists_uniform_fourierTruncation_sq_bound_iff_halfGeneratorDomain
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.tendsto_criticalMildImageFourierTruncation
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.fixedPoint_uniform_fourier_sq_iff_graph
#print axioms Navier.Analysis.LeiLinPositiveRestartFourier.fixedPoint_not_exists_uniform_fourier_sq_of_not_graph
