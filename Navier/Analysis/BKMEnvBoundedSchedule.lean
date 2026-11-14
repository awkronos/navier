/-
Original work, lane MSW-NAVIER-1114 (2026-11-14).

# The BKM envelope chain on a schedule that keeps its cut-stage bounds

`BKMEnvAxis.aSel` is `Classical.choose` of `ActualCandidateAssembly.selected_witness`.
That witness records `MixedCandidateWitness.SelectedSchedule`, which holds the
schedule's growth, smoothness and residual facts but not the cut-stage bounds
`MixedDiagonalSchedule.ThreeCutBounds`: those are proved for the schedule by
`MixedDiagonalResidual.exists_physical_schedule_residual_zero` and dropped one
step later.  The negative-power envelope
`CSPotentialSumEnvelope.potentialSum_negPower_envelope` consumes exactly those
bounds (`DiagonalJetBounds.CutStageBounds`), so for `aSel` its hypothesis has no
source in the repository.

This module moves the chain to the schedule `aB` of
`BoundedScheduleWitness.actual_bounded_witness`, which is selected, has the
candidate properties, and keeps the three cut-stage bounds.  For `uSel aB`:

* the field smoothness and both slice-smoothness inputs of
  `BKMEnvCut.polyUpper_of_cylSums` are proved here;
* the rate bound is conditional only on the two cylinder-sup power bounds.

Status: conditional.  The two cylinder-sup bounds `hA`, `hB` remain open; this
module does not prove them and does not prove `VorticityRateBound (uSel aB)`.
-/
import Navier.Analysis.BKMEnvCut
import Navier.Construction.BoundedScheduleWitness

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ContDiff
open Navier Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Analysis.BKMProfileRateBound
open Navier.Analysis.BKMProfileSelectedEnvelope
open Navier.Construction ProblemStatement SpatialCurl
open Navier.Construction.CorrectionInitialization
open Navier.Construction.CorrectionInitialization.ActualPrimary
open Navier.Analysis.BKMEnvAxis

namespace Navier.Analysis.BKMEnvBoundedSchedule

/-- The selected schedule that keeps its cut-stage bounds. -/
noncomputable def aB : ℕ → ℕ :=
  Classical.choose (BoundedScheduleWitness.actual_bounded_witness
    ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry)

/-- `aB` is a selected schedule for the selected stages. -/
theorem aB_selected :
    MixedCandidateWitness.SelectedSchedule h qbigSel
      ActualCandidateAssembly.selectedPotentialStages
      ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages aB :=
  (Classical.choose_spec (BoundedScheduleWitness.actual_bounded_witness
    ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry)).1

/-- The gain of the selected stage estimates. -/
noncomputable def gainSel : ℕ → ℝ :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).gain

/-- The common derivative loss of the selected stage estimates. -/
noncomputable def lossSel : ℕ → ℝ :=
  MixedDiagonalSchedule.commonLoss
    (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry).potentialLoss
    (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry).directLoss
    (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry).pressureLoss

/-- `aB` keeps the three cut-stage bounds on the preterminal region.  This is
the fact the witness schedule `aSel` does not record. -/
theorem aB_cutBounds :
    MixedDiagonalSchedule.ThreeCutBounds aB h
      ActualCandidateAssembly.selectedPotentialStages
      ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages
      (fun j => gainSel j / 2) lossSel PhysicalWaveSum.preterminal :=
  (Classical.choose_spec (BoundedScheduleWitness.actual_bounded_witness
    ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry)).2.1

/-- The compact candidate built on `aB` has the candidate properties. -/
theorem aB_candidate :
    ∃ forcing : ProblemStatement.VelocityField,
      CandidateProperties (R3CompactCandidate.periodicVelocity (ASum aB) (BSum aB))
        (R3CompactCandidate.periodicPressure (PSum aB)) forcing :=
  (Classical.choose_spec (BoundedScheduleWitness.actual_bounded_witness
    ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry)).2.2

/-- The assembled field on `aB` is smooth before the singular time. -/
theorem uSel_aB_smooth : ContDiffOn ℝ ∞ (uSel aB) preSingularDomain := by
  obtain ⟨forcing, hc⟩ := aB_candidate
  exact (R3CompactCandidate.of_localized_fields hc).velocity_smooth

/-- Every spatial slice of the potential sum on `aB` before time one is smooth. -/
theorem ASum_aB_slice_smooth {t : ℝ} (ht : t < 1) :
    ContDiffOn ℝ ∞ (fun x : ProblemStatement.Space => ASum aB (t, x)) univ := by
  obtain ⟨_, _, _, _, _, _, hs, _⟩ := aB_selected
  exact hs.potential.comp (contDiff_prodMk_right t).contDiffOn (fun x _ => ht)

/-- Every spatial slice of the direct sum on `aB` before time one is smooth. -/
theorem BSum_aB_slice_smooth {t : ℝ} (ht : t < 1) :
    ContDiffOn ℝ ∞ (fun x : ProblemStatement.Space => BSum aB (t, x)) univ := by
  obtain ⟨_, _, _, _, _, _, hs, _⟩ := aB_selected
  exact hs.direct.comp (contDiff_prodMk_right t).contDiffOn (fun x _ => ht)

/-- The polynomial upper envelope for `uSel aB` from the two cylinder-sup power
bounds alone: the three smoothness inputs are proved for this schedule. -/
theorem polyUpper_aB_of_cylSums
    {β : ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hA : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ (SpatialLocalization.supportCylinder :
        Set ProblemStatement.Space),
        ‖spatialCurl (SpatialLocalization.cutVelocity (ASum aB)) (t, x)‖ ≤ c₁ * (1 - t) ^ (-β))
    (hB : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ (SpatialLocalization.supportCylinder :
        Set ProblemStatement.Space),
        ‖spatialCurl (SpatialLocalization.cutPotential (BSum aB)) (t, x)‖ ≤ c₂ * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), V (uSel aB) t ≤ (c₁ + c₂) * (1 - t) ^ (-β) :=
  BKMEnvCut.polyUpper_of_cylSums uSel_aB_smooth hc₁ hc₂ ht₀
    (fun _ ht => ASum_aB_slice_smooth ht.2) (fun _ ht => BSum_aB_slice_smooth ht.2) hA hB

/-- The vorticity rate bound for the compact candidate on `aB`, conditional
only on the two cylinder-sup power bounds. -/
theorem vorticityRateBound_aB_of_cylSums
    {β : ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hA : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ (SpatialLocalization.supportCylinder :
        Set ProblemStatement.Space),
        ‖spatialCurl (SpatialLocalization.cutVelocity (ASum aB)) (t, x)‖ ≤ c₁ * (1 - t) ^ (-β))
    (hB : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ (SpatialLocalization.supportCylinder :
        Set ProblemStatement.Space),
        ‖spatialCurl (SpatialLocalization.cutPotential (BSum aB)) (t, x)‖ ≤ c₂ * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aB) := by
  obtain ⟨forcing, hc⟩ := aB_candidate
  exact vorticityRateBound_of_polyUpper aB_selected hc (add_nonneg hc₁ hc₂)
    ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans ht₀.1, ht₀.2⟩
    (polyUpper_aB_of_cylSums hc₁ hc₂ ht₀ hA hB)

end Navier.Analysis.BKMEnvBoundedSchedule

#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_selected
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_cutBounds
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_candidate
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.uSel_aB_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.ASum_aB_slice_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.BSum_aB_slice_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.polyUpper_aB_of_cylSums
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_cylSums
