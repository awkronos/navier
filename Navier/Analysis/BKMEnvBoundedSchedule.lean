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
Lane MSW-NAVIER-VRTY-1114 (2026-11-14) added `vorticityRateBound_aB_of_rawJets`:
the same rate bound under ONE named hypothesis — a raw slice-jet envelope of
the two sums at orders `≤ 2` — by way of transport T3 in `BKMEnvCut`.  That raw
envelope is itself still open (it is transport T1's missing low-stage table
`hK`, whose output format `CS_PotentialSumEnvelope` emits), so nothing here
discharges `VorticityRateBound (uSel aB)` and the `hA`/`hB` bounds above remain
unproved.

Lane MSW-NAVIER-HK-1114 (2026-11-15) supplies the missing `hK` table in
`CS_PotentialSumEnvelope` (`lowStageTable`, `lowStageTable_le`,
`potentialSum_negPower_envelope_of_cutBounds`) and the spacetime-to-slice jet
leg in `BKMEnvCut` (`norm_iteratedFDeriv_slice_le`), and adds below
`rawJets_aB_of_posAndInitial`: the carrier's raw slice-jet envelope follows
from the positive-stage envelope and the stage-zero term, using
`MixedDiagonalSchedule.physical_initial_split_jets`.  This is still a
reduction, not a discharge: the two inputs it names are hypotheses here, the
positive-stage one itself carrying `CS_PotentialSumEnvelope`'s undischarged
side condition `hnum`, and `VorticityRateBound (uSel aB)` remains unproved.

Lane MSW-NAVIER-P1-1114 (2026-11-15) closes the regularity gap that made that
reduction the last one available.  `StageEstimates.potential_smooth` /
`direct_smooth` plus `aB_selected`'s scale gap feed
`CutStageEstimates.cut_product_smooth_of_sublevel`, so each `aB` cut stage
extends smoothly by zero to all of `PhysicalWaveSum.preterminal`
(`cutStage_aB_contDiffOn`), and local finiteness sums that to
`positiveSum_aB_contDiffOn` — the preterminal smoothness of the positive-stage
sums, which the repository did not have for any fixed schedule before.  Both
summands of the initial split are now smooth, so `iteratedFDeriv_add` runs on
them (`iteratedFDeriv_potentialSum_aB_split`) and the carrier's raw envelope can
be assembled from one bound per summand
(`rawJetsASum_of_splitJets`, `rawJetsBSum_of_splitJets`,
`vorticityRateBound_aB_of_splitJets`).  Still a reduction: `VorticityRateBound
(uSel aB)` is discharged by no row here, and the four pointwise slice-jet bounds
`rawJetsSplit_aB_of_twoSliceJets` asks for are exactly what transports T1 (with
`hnum`) and T2 must supply.

Lane MSW-NAVIER-INST-1114 (2026-11-15) instantiates BOTH composer envelopes at
the actual schedule `aB` (`negPowerEnvelope_aB_potential`,
`negPowerEnvelope_aB_direct`) by running
`CSPotentialSumEnvelope.potentialSum_negPower_envelope_of_cutBounds` on the
open sublevel `CutStageEstimates.physicalSublevel h qbigSel`, where its
per-stage hypothesis is the trunk record field, and extending the conclusion
pointwise to all of `PhysicalWaveSum.preterminal` through the germ-zero rows
(`cut_product_eventually_zero` at the scale gap `aB_gap_mul` plus
`eventually_zero_tail`).  The composer's raw-stage smoothness gap is thereby
closed without new analysis.  The near-terminal row
`vorticityRateBound_aB_of_hnum_and_stageZero` leaves `VorticityRateBound
(uSel aB)` conditional on exactly `hnum`'s three inequalities and the two
transport-T2 stage-zero slice rows.

Lane KGV-NAVIER-1121 (2026-11-20) falsifies that hypothesis instead of
carrying it.  `not_hnum_aB` below is `Construction.HnumFalsification.not_hnum`
at the selected estimates — `∀ m ≤ 2, 0 ≤ gainSel 1 / 2 - lossSel m` is FALSE,
not merely undischarged.  `negPowerEnvelope_aB_potential`,
`negPowerEnvelope_aB_direct`, `negPowerEnvelope_aB_preterminal` and
`vorticityRateBound_aB_of_hnum_and_stageZero` all had `hnum` as a hypothesis
and so could never be applied; they are removed.  Their unconditional
counterparts from `CS_PotentialSumEnvelopeGrowth` (the `_free` rows and
`vorticityRateBound_aB_of_stageZero`) were already the live route and are
unchanged.  Nothing in the repository referenced the removed rows from
outside this file.
-/
import Mathlib.Order.Filter.Finite
import Navier.Analysis.BKMEnvCut
import Navier.Construction.CS_PotentialSumEnvelope
import Navier.Construction.CS_PotentialSumEnvelopeGrowth
import Navier.Construction.BoundedScheduleWitness
import Navier.Construction.HnumFalsification

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ContDiff
open Navier Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Analysis.BKMProfileGronwallPair Navier.Analysis.BKMProfileRateBound
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

/-- **`hnum` is uninhabitable at `gainSel`/`lossSel`.**  This is exactly the
hypothesis the `CSPotentialSumEnvelope` producer needs at ceiling `M = 2`
(see the `Transport T1` section below).  `Construction.HnumFalsification.not_hnum`
discharges it to `False` at every admissible estimate record, and the
definitional unfolding of `gainSel`/`lossSel` at the selected record
(`selectedBudget`, `selectedThreshold`, `selectedThreshold_geometry`) is
verbatim its instance there; no `Classical.choose` appears in the three
functions `not_hnum` reasons about, only in the constant fields and the
schedule `aB` itself. -/
theorem not_hnum_aB : ¬ (∀ m ≤ 2, (0 : ℝ) ≤ gainSel 1 / 2 - lossSel m) :=
  HnumFalsification.not_hnum ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry

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

/-- **Transport T3 on the bounded schedule.** A single named hypothesis — a
raw slice-jet envelope of the two sums on `aB`, at orders `≤ 2` and one rate
`β` — gives `VorticityRateBound (uSel aB)`.  The two cylinder-sup power bounds
`hA`, `hB` of `vorticityRateBound_aB_of_cylSums` are discharged here from the
raw jets through `BKMEnvCut.cutVelocity_cylSup_le_rawJets` and
`BKMEnvCut.cutPotential_cylSup_le_rawJets`, at the explicit constants
`4 · ‖curlLinear‖² · cutJetBound · c` and `2 · ‖curlLinear‖ · cutJetBound · c`.
The residual obligation is now the raw envelope itself: transport T1's missing
low-stage table `hK`.  Satisfiable: a spatially constant slice satisfies it at
rate `β = 0`. -/
theorem vorticityRateBound_aB_of_rawJets
    {β : ℝ} {c : ℝ} (hc : 0 ≤ c)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hjetA : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
        ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
          ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => ASum aB (t, x)) x‖ ≤
            c * (1 - t) ^ (-β))
    (hjetB : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
        ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
          ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => BSum aB (t, x)) x‖ ≤
            c * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aB) := by
  have hcA : 0 ≤ (4 : ℝ) * ‖curlLinear‖ ^ 2 * BKMEnvCut.cutJetBound * c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 ≤ ‖curlLinear‖ ^ 2)) BKMEnvCut.cutJetBound_nonneg) hc
  have hcB : 0 ≤ (2 : ℝ) * ‖curlLinear‖ * BKMEnvCut.cutJetBound * c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 ≤ ‖curlLinear‖)) BKMEnvCut.cutJetBound_nonneg) hc
  refine vorticityRateBound_aB_of_cylSums (β := β) hcA hcB ht₀ ?_ ?_
  · intro t ht
    exact BKMEnvCut.cutVelocity_cylSup_le_rawJets
      ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans (ht₀.1.trans ht.1), ht.2⟩
      (ASum_aB_slice_smooth ht.2) hc (hjetA t ht)
  · intro t ht
    exact BKMEnvCut.cutPotential_cylSup_le_rawJets
      ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans (ht₀.1.trans ht.1), ht.2⟩
      (BSum_aB_slice_smooth ht.2) hc (hjetB t ht)

/-! ## Transport T2 made explicit

The raw sums `ASum aB` / `BSum aB` keep their stage-zero term, while the
positive-stage object that `CS_PotentialSumEnvelope` bounds does not.
`MixedDiagonalSchedule.physical_initial_split_jets` is the exact bridge: at every
preterminal spacetime point the jet of the raw sum is the jet of the single
function "stage zero plus the positive-stage sum".  Together with the slice leg
`BKMEnvCut.norm_iteratedFDeriv_slice_le` this turns the carrier's raw slice-jet
envelope into a spacetime-jet envelope of that displayed sum, which is the
format the two remaining transports emit: `CSPotentialSumEnvelope` for the
positive-stage summand, transport T2 for the initial stage. -/

/-- The origin lies in the spatial support cylinder. -/
private theorem zero_mem_cylB :
    (0 : ProblemStatement.Space) ∈ (SpatialLocalization.supportCylinder :
      Set ProblemStatement.Space) := by
  simp [SpatialLocalization.supportCylinder, SpatialLocalization.radialSquare]

/-- **Cylinder-sup packaging.** A pointwise bound and a pointwise lower bound
transfer to the iterated cylinder supremum: `cbiSup_eq_ciSup_subtype` rewrites
the iterated sup to a sup over the subtype (its two side conditions are the
boundedness the pointwise bound itself supplies, and the empty-case default
`sSup ∅ = 0 ≤ sup`), then `ciSup_le` finishes.  No compactness is used. -/
private theorem cylBSup_le {g : ProblemStatement.Space → ℝ} {c : ℝ}
    (hgnn : ∀ x : ProblemStatement.Space, 0 ≤ g x)
    (h : ∀ x : ProblemStatement.Space, g x ≤ c)
    (hbdd : BddAbove (Set.range (fun a : { x // x ∈ (SpatialLocalization.supportCylinder :
        Set ProblemStatement.Space) } => g a.1))) :
    ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space), g x ≤ c := by
  haveI : Nonempty { x : ProblemStatement.Space //
      x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space) } :=
    ⟨⟨0, zero_mem_cylB⟩⟩
  rw [cbiSup_eq_ciSup_subtype (p := fun x : ProblemStatement.Space =>
        x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space))
    (f := fun (x : ProblemStatement.Space)
      (_ : x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space)) => g x)
    hbdd (by rw [Real.sSup_empty]; exact (hgnn 0).trans (le_ciSup hbdd ⟨0, zero_mem_cylB⟩))]
  exact ciSup_le fun a => h a.1

/-- **The carrier's raw slice-jet envelope, reduced (potential sum).** If the
spacetime jets at orders `≤ 2` of the displayed sum "initial stage of
`selectedPotentialStages` plus the positive-stage potential sum" are bounded on
`{t} × Space` by `c · (1 - t) ^ (-β)`, then the slice-jet envelope `hjetA` of
`vorticityRateBound_aB_of_rawJets` holds with the same constant.  Mechanism: the
slice jet is at most the spacetime jet (`BKMEnvCut.norm_iteratedFDeriv_slice_le`,
whose smoothness input is `aB_selected`'s preterminal
`ThreeSmoothSums.potential`), and the spacetime jet of `ASum aB` is exactly the
spacetime jet of that displayed sum (`physical_initial_split_jets`).  Reduction,
not discharge: the hypothesis is a named input, and it is the two remaining
transports (T1's positive-stage envelope with its side condition `hnum`, and T2
for the initial stage) that would have to supply it. -/
theorem rawJetsASum_of_spaceJets
    {β : ℝ} {c : ℝ} {t₀ : ℝ}
    (hjet : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedPotentialStages 0 z +
              SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                (PhysicalWaveSum.physicalQ h)
                (CutStageEstimates.positiveStages
                  ActualCandidateAssembly.selectedPotentialStages) z) (t, x)‖ ≤
          c * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
      ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => ASum aB (t, x)) x‖ ≤
          c * (1 - t) ^ (-β) := by
  obtain ⟨_, _, _, ham, _, _, hs, _⟩ := aB_selected
  intro t ht k hk
  have hmem : ∀ y : ProblemStatement.Space, (t, y) ∈ PhysicalWaveSum.preterminal := fun _ => ht.2
  have hpt : ∀ y : ProblemStatement.Space,
      ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => ASum aB (t, x)) y‖ ≤
        c * (1 - t) ^ (-β) := by
    intro y
    have hsplit : iteratedFDeriv ℝ k (ASum aB) (t, y) =
        iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedPotentialStages 0 z +
            SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (CutStageEstimates.positiveStages
                ActualCandidateAssembly.selectedPotentialStages) z) (t, y) :=
      MixedDiagonalSchedule.physical_initial_split_jets (hh := outgoing.data.h_pos)
        (hh1 := outgoing.data.h_lt_half) (ha := ham)
        (A := ActualCandidateAssembly.selectedPotentialStages) (w := (t, y)) (hmem y) k
    calc ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => ASum aB (t, x)) y‖
        ≤ ‖iteratedFDeriv ℝ k (ASum aB) (t, y)‖ :=
              BKMEnvCut.norm_iteratedFDeriv_slice_le (f := ASum aB)
                PhysicalWaveSum.preterminal_open hs.potential t hmem y k
        _ = ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
                SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
                  ActualCandidateAssembly.selectedPotentialStages 0 z +
                  SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                    (PhysicalWaveSum.physicalQ h)
                    (CutStageEstimates.positiveStages
                      ActualCandidateAssembly.selectedPotentialStages) z) (t, y)‖ :=
              congrArg (fun v => ‖v‖) hsplit
        _ ≤ c * (1 - t) ^ (-β) := hjet t ht k hk y
  refine cylBSup_le (fun _ => norm_nonneg _) hpt ?_
  refine ⟨c * (1 - t) ^ (-β), fun y hy => ?_⟩
  rcases hy with ⟨a, rfl⟩
  exact hpt a.1

/-- **The carrier's raw slice-jet envelope, reduced (direct sum).** The same
reduction for `BSum aB`, reading smoothness from `aB_selected`'s
`ThreeSmoothSums.direct` and splitting at the initial stage of
`ActualCandidateAssembly.selectedDirectStages`. -/
theorem rawJetsBSum_of_spaceJets
    {β : ℝ} {c : ℝ} {t₀ : ℝ}
    (hjet : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedDirectStages 0 z +
              SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                (PhysicalWaveSum.physicalQ h)
                (CutStageEstimates.positiveStages
                  ActualCandidateAssembly.selectedDirectStages) z) (t, x)‖ ≤
          c * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
      ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => BSum aB (t, x)) x‖ ≤
          c * (1 - t) ^ (-β) := by
  obtain ⟨_, _, _, ham, _, _, hs, _⟩ := aB_selected
  intro t ht k hk
  have hmem : ∀ y : ProblemStatement.Space, (t, y) ∈ PhysicalWaveSum.preterminal := fun _ => ht.2
  have hpt : ∀ y : ProblemStatement.Space,
      ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => BSum aB (t, x)) y‖ ≤
        c * (1 - t) ^ (-β) := by
    intro y
    have hsplit : iteratedFDeriv ℝ k (BSum aB) (t, y) =
        iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedDirectStages 0 z +
            SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (CutStageEstimates.positiveStages
                ActualCandidateAssembly.selectedDirectStages) z) (t, y) :=
      MixedDiagonalSchedule.physical_initial_split_jets (hh := outgoing.data.h_pos)
        (hh1 := outgoing.data.h_lt_half) (ha := ham)
        (A := ActualCandidateAssembly.selectedDirectStages) (w := (t, y)) (hmem y) k
    calc ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => BSum aB (t, x)) y‖
        ≤ ‖iteratedFDeriv ℝ k (BSum aB) (t, y)‖ :=
              BKMEnvCut.norm_iteratedFDeriv_slice_le (f := BSum aB)
                PhysicalWaveSum.preterminal_open hs.direct t hmem y k
        _ = ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
                SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
                  ActualCandidateAssembly.selectedDirectStages 0 z +
                  SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                    (PhysicalWaveSum.physicalQ h)
                    (CutStageEstimates.positiveStages
                      ActualCandidateAssembly.selectedDirectStages) z) (t, y)‖ :=
              congrArg (fun v => ‖v‖) hsplit
        _ ≤ c * (1 - t) ^ (-β) := hjet t ht k hk y
  refine cylBSup_le (fun _ => norm_nonneg _) hpt ?_
  refine ⟨c * (1 - t) ^ (-β), fun y hy => ?_⟩
  rcases hy with ⟨a, rfl⟩
  exact hpt a.1

/-- **The spacetime-jet envelope gives the rate bound.** Feeding the two
reductions above into `vorticityRateBound_aB_of_rawJets`.  Named hypotheses, no
discharge: `hjetA`/`hjetB` ask for spacetime jets (not slice jets) of the
displayed "initial stage + positive-stage sum" functions, which is what
`CSPotentialSumEnvelope.potentialSum_negPower_envelope_of_cutBounds` would have
to reach for the positive summand (with its undischarged side condition `hnum`
at `M = 2`, and the region and per-stage smoothness inputs it asks for) together
with transport T2 for the initial stage.  Nothing here proves
`VorticityRateBound (uSel aB)`. -/
theorem vorticityRateBound_aB_of_spaceJets
    {β : ℝ} {c : ℝ} (hc : 0 ≤ c)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hjetA : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedPotentialStages 0 z +
              SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                (PhysicalWaveSum.physicalQ h)
                (CutStageEstimates.positiveStages
                  ActualCandidateAssembly.selectedPotentialStages) z) (t, x)‖ ≤
          c * (1 - t) ^ (-β))
    (hjetB : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
            SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              ActualCandidateAssembly.selectedDirectStages 0 z +
              SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
                (PhysicalWaveSum.physicalQ h)
                (CutStageEstimates.positiveStages
                  ActualCandidateAssembly.selectedDirectStages) z) (t, x)‖ ≤
          c * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aB) :=
  vorticityRateBound_aB_of_rawJets hc ht₀
    (rawJetsASum_of_spaceJets hjetA)
    (rawJetsBSum_of_spaceJets hjetB)

/-! ## PRIORITY 1 — preterminal smoothness of the positive-stage sums

`MixedCandidateAssembly.StageEstimates.potential_smooth` / `direct_smooth` say
the selected stages are smooth on the *open* sublevel
`CutStageEstimates.physicalSublevel h qbigSel`, and `aB_selected` records the
diagonal scale gap `∀ j, 1 / (aB j : ℝ) < qbigSel`.  Those are exactly the two
hypotheses `CutStageEstimates.cut_product_smooth_of_sublevel` consumes, so every
cut product `SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (physicalQ h) A j`
extends smoothly by zero across all of `PhysicalWaveSum.preterminal`;
`SolenoidalDiagonal.eventually_zero_tail` then makes the diagonal sum a finite
sum on a neighbourhood of each preterminal point, and
`DiagonalJetBounds.tsum_jet_identity` transfers that to the sum itself.

This is the input the split was missing.  With BOTH summands smooth,
`iteratedFDeriv_add_apply` applies, so `rawJetsASum_of_splitJets` /
`rawJetsBSum_of_splitJets` ask the remaining transports for one envelope per
summand (the positive-stage sum from `CSPotentialSumEnvelope`, the initial stage
from transport T2) instead of one envelope on the displayed sum, and
`vorticityRateBound_aB_of_splitJets` discharges `VorticityRateBound (uSel aB)`
from those four pointwise slice-jet bounds.  Nothing here proves those bounds. -/

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- The selected potential stages are smooth on the open physical sublevel
region: the `potential_smooth` field of the selected `StageEstimates` record. -/
theorem selectedPotentialStages_smooth_physicalSublevel (j : ℕ) :
    ContDiffOn ℝ ∞ (ActualCandidateAssembly.selectedPotentialStages j)
      (CutStageEstimates.physicalSublevel h qbigSel) :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).potential_smooth j

/-- The same region fact for the selected direct stages (`direct_smooth`). -/
theorem selectedDirectStages_smooth_physicalSublevel (j : ℕ) :
    ContDiffOn ℝ ∞ (ActualCandidateAssembly.selectedDirectStages j)
      (CutStageEstimates.physicalSublevel h qbigSel) :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).direct_smooth j

/-- Fourth field of `aB_selected`. -/
private theorem aB_strictMono : StrictMono aB := by
  obtain ⟨_, _, _, ham, _, _, _, _⟩ := aB_selected
  exact ham

/-- Fifth field of `aB_selected`: the realisation of the schedule diverges. -/
private theorem aB_tendsto_real : Tendsto (fun j => (aB j : ℝ)) atTop atTop := by
  obtain ⟨_, _, _, _, hat, _, _, _⟩ := aB_selected
  exact hat

private theorem aB_pos_real (j : ℕ) : (0 : ℝ) < (aB j : ℝ) := by
  obtain ⟨_, hap, _, _, _, _, _, _⟩ := aB_selected
  exact_mod_cast hap j

/-- Sixth field of `aB_selected`: every scale reciprocal lies below `qbigSel`. -/
private theorem aB_scale_gap (j : ℕ) : 1 / (aB j : ℝ) < qbigSel := by
  obtain ⟨_, _, _, _, _, hgap, _, _⟩ := aB_selected
  exact hgap j

/-- The scale gap in the multiplicative form the zero-extension lemma wants. -/
private theorem aB_gap_mul (j : ℕ) : 1 < (aB j : ℝ) * qbigSel := by
  have hp := aB_pos_real j
  simpa only [mul_comm] using (div_lt_iff₀ hp).mp (aB_scale_gap j)

private theorem physicalQ_contDiffOn_preterminal :
    ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) PhysicalWaveSum.preterminal :=
  fun _w hw => (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
    outgoing.data.h_lt_half hw).contDiffWithinAt

/-- **Every cut stage, extended by zero to all preterminal spacetime.**  The
sublevel smoothness of the stage plus the scale gap `1 < (aB j : ℝ) * qbigSel`
give the zero extension; no regularity of the stage outside the sublevel is
charged. -/
theorem cutStage_aB_contDiffOn {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    (j : ℕ) :
    ContDiffOn ℝ ∞ (SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) A j) PhysicalWaveSum.preterminal := by
  refine CutStageEstimates.cut_product_smooth_of_sublevel PhysicalWaveSum.preterminal_open
    physicalQ_contDiffOn_preterminal ?_ (aB_pos_real j) (aB_gap_mul j)
  exact hA j

/-- The positive-stage sum is smooth at one preterminal point: local finiteness
(`eventually_zero_tail`) reduces it to a finite sum of the previous lemma. -/
theorem positiveSum_aB_contDiffAt {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal) :
    ContDiffAt ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w := by
  refine (DiagonalJetBounds.tsum_jet_identity
    (SolenoidalDiagonal.eventually_zero_tail aB_tendsto_real
      ((PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
        outgoing.data.h_lt_half hw).continuousAt)
      (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw)
      (CutStageEstimates.positiveStages A)) ?_).1
  intro j
  exact (cutStage_aB_contDiffOn
    (CutStageEstimates.positiveStages_smooth (fun i _ => hA i)) j).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)

/-- The summation half of **PRIORITY 1**, parametric in the stage sequence. -/
theorem positiveSum_aB_contDiffOn {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel)) :
    ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A))
      PhysicalWaveSum.preterminal :=
  fun _w hw => (positiveSum_aB_contDiffAt hA hw).contDiffWithinAt

/-- **PRIORITY 1 (potential).** The positive-stage sum of the selected potential
stages on the bounded schedule `aB` is smooth on the whole preterminal region. -/
theorem positivePotentialSum_aB_contDiffOn :
    ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h)
      (CutStageEstimates.positiveStages ActualCandidateAssembly.selectedPotentialStages))
      PhysicalWaveSum.preterminal :=
  positiveSum_aB_contDiffOn (A := ActualCandidateAssembly.selectedPotentialStages)
    selectedPotentialStages_smooth_physicalSublevel

/-- **PRIORITY 1 (direct).** The same row for the selected direct stages. -/
theorem positiveDirectSum_aB_contDiffOn :
    ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h)
      (CutStageEstimates.positiveStages ActualCandidateAssembly.selectedDirectStages))
      PhysicalWaveSum.preterminal :=
  positiveSum_aB_contDiffOn (A := ActualCandidateAssembly.selectedDirectStages)
    selectedDirectStages_smooth_physicalSublevel

/-- **The `iteratedFDeriv_add` split the carrier could not run.**  At a
preterminal point the `k`-jet of the raw selected sum is the sum of the
initial-stage jet and the positive-stage jet.  `MixedDiagonalSchedule.
physical_initial_split_jets` alone only rewrites the jet of the raw sum into the
jet of the *displayed* sum; splitting that jet needs both summands smooth, which
is the content of `cutStage_aB_contDiffOn` and `positiveSum_aB_contDiffOn`. -/
theorem iteratedFDeriv_potentialSum_aB_split {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    (k : ℕ) {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal) :
    iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) A) w =
      iteratedFDeriv ℝ k (SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) A 0) w
    + iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w := by
  have hsplit : iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum
      (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A) w =
      iteratedFDeriv ℝ k (fun z : ProblemStatement.SpaceTime =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 z +
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) z) w :=
    MixedDiagonalSchedule.physical_initial_split_jets (hh := outgoing.data.h_pos)
      (hh1 := outgoing.data.h_lt_half) (ha := aB_strictMono) (A := A) (w := w) hw k
  rw [hsplit]
  refine iteratedFDeriv_add_apply
    (f := fun z : ProblemStatement.SpaceTime => SolenoidalDiagonal.cutStage
      (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 z)
    (g := fun z : ProblemStatement.SpaceTime => SolenoidalDiagonal.potentialSum
      (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages A) z) ?_ ?_
  · exact ((cutStage_aB_contDiffOn hA 0).contDiffAt
      (PhysicalWaveSum.preterminal_open.mem_nhds hw)).of_le (nat_le_infty k)
  · exact (positiveSum_aB_contDiffAt hA hw).of_le (nat_le_infty k)

/-- The potential row of the split, at the retained raw sum `ASum aB`. -/
theorem iteratedFDeriv_ASum_aB_split (k : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    iteratedFDeriv ℝ k (ASum aB) w =
      iteratedFDeriv ℝ k (SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) ActualCandidateAssembly.selectedPotentialStages 0) w
    + iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages ActualCandidateAssembly.selectedPotentialStages)) w :=
  iteratedFDeriv_potentialSum_aB_split (A := ActualCandidateAssembly.selectedPotentialStages)
    selectedPotentialStages_smooth_physicalSublevel k hw

/-- The direct row of the split, at the retained raw sum `BSum aB`. -/
theorem iteratedFDeriv_BSum_aB_split (k : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    iteratedFDeriv ℝ k (BSum aB) w =
      iteratedFDeriv ℝ k (SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) ActualCandidateAssembly.selectedDirectStages 0) w
    + iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages ActualCandidateAssembly.selectedDirectStages)) w :=
  iteratedFDeriv_potentialSum_aB_split (A := ActualCandidateAssembly.selectedDirectStages)
    selectedDirectStages_smooth_physicalSublevel k hw

/-- Two summand envelopes add to one envelope of the raw selected sum at a
preterminal point. -/
theorem norm_potentialSum_aB_le_split {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    {k : ℕ} {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    {B₀ B₁ : ℝ}
    (h0 : ‖iteratedFDeriv ℝ k (SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) A 0) w‖ ≤ B₀)
    (h1 : ‖iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w‖ ≤ B₁) :
    ‖iteratedFDeriv ℝ k (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) A) w‖ ≤ B₀ + B₁ := by
  rw [iteratedFDeriv_potentialSum_aB_split hA k hw]
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

/-- **Two envelopes, one per summand, give the carrier's raw slice-jet
envelope.**  Where `rawJetsASum_of_spaceJets` assumes one bound on the displayed
"initial stage + positive-stage sum", this row assumes a bound on each summand's
slice jet separately — which is what `CSPotentialSumEnvelope` emits for the
positive summand and transport T2 emits for the initial stage — and derives the
cylinder-sup row `hjetA` of `vorticityRateBound_aB_of_rawJets` at the summed
constant.  The slice jets split because both summands are smooth on preterminal
(`iteratedFDeriv_potentialSum_aB_split`, transported to the slice by composing
with `fun x => (t, x)`); the pointwise-to-cylinder step is `cylBSup_le`. -/
theorem rawJetsSplit_aB_of_twoSliceJets {A : ℕ → ProblemStatement.VelocityField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    {β : ℝ} {c₀ c₁ : ℝ} {t₀ : ℝ}
    (hjet0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            A 0 (t, x)) x‖ ≤ c₀ * (1 - t) ^ (-β))
    (hjet1 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) (t, x)) x‖ ≤ c₁ * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
      ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            A (t, x)) x‖ ≤ (c₀ + c₁) * (1 - t) ^ (-β) := by
  intro t ht k hk
  have hmap : ∀ y : ProblemStatement.Space, (t, y) ∈ PhysicalWaveSum.preterminal :=
    fun _ => ht.2
  have hs0 : ContDiffOn ℝ ∞ (fun x : ProblemStatement.Space => SolenoidalDiagonal.cutStage
      (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 (t, x)) univ :=
    (cutStage_aB_contDiffOn hA 0).comp (contDiff_prodMk_right t).contDiffOn fun x _ => hmap x
  have hs1 : ContDiffOn ℝ ∞ (fun x : ProblemStatement.Space => SolenoidalDiagonal.potentialSum
      (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
      (CutStageEstimates.positiveStages A) (t, x)) univ :=
    (positiveSum_aB_contDiffOn hA).comp (contDiff_prodMk_right t).contDiffOn fun x _ => hmap x
  have hpt : ∀ y : ProblemStatement.Space,
      ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            A (t, x)) y‖ ≤ (c₀ + c₁) * (1 - t) ^ (-β) := by
    intro y
    have hgerm : (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) A) =ᶠ[𝓝 (t, y)]
        (fun z : ProblemStatement.SpaceTime =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 z +
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) z) :=
      MixedDiagonalSchedule.physical_initial_split_germ (hh := outgoing.data.h_pos)
        (hh1 := outgoing.data.h_lt_half) (ha := aB_strictMono) (A := A) (hmap y)
    have hslice := SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
      (hgerm.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt) k
    have heq : iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            A (t, x)) y =
        iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => SolenoidalDiagonal.cutStage
          (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 (t, x)) y +
          iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
            SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (CutStageEstimates.positiveStages A) (t, x)) y :=
      hslice.self_of_nhds.trans
        (iteratedFDeriv_add_apply (f := fun x : ProblemStatement.Space => SolenoidalDiagonal.cutStage
            (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0 (t, x))
          (g := fun x : ProblemStatement.Space => SolenoidalDiagonal.potentialSum
            (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (CutStageEstimates.positiveStages A) (t, x))
          ((hs0.contDiffAt univ_mem).of_le (nat_le_infty k))
          ((hs1.contDiffAt univ_mem).of_le (nat_le_infty k)))
    rw [heq]
    exact (norm_add_le _ _).trans
      ((add_le_add (hjet0 t ht k hk y) (hjet1 t ht k hk y)).trans
        (le_of_eq ((add_mul c₀ c₁ ((1 - t) ^ (-β))).symm)))
  refine cylBSup_le (fun _ => norm_nonneg _) hpt ?_
  refine ⟨(c₀ + c₁) * (1 - t) ^ (-β), fun y hy => ?_⟩
  rcases hy with ⟨a, rfl⟩
  exact hpt a.1

/-- The potential row of the two-summand packaging at `ASum aB`. -/
theorem rawJetsASum_of_splitJets {β : ℝ} {c₀ c₁ : ℝ} {t₀ : ℝ}
    (hjet0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedPotentialStages 0 (t, x)) x‖ ≤
              c₀ * (1 - t) ^ (-β))
    (hjet1 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedPotentialStages) (t, x)) x‖ ≤
              c₁ * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
      ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => ASum aB (t, x)) x‖ ≤
          (c₀ + c₁) * (1 - t) ^ (-β) :=
  rawJetsSplit_aB_of_twoSliceJets selectedPotentialStages_smooth_physicalSublevel
    hjet0 hjet1

/-- The direct row of the two-summand packaging at `BSum aB`. -/
theorem rawJetsBSum_of_splitJets {β : ℝ} {c₀ c₁ : ℝ} {t₀ : ℝ}
    (hjet0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedDirectStages 0 (t, x)) x‖ ≤
              c₀ * (1 - t) ^ (-β))
    (hjet1 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedDirectStages) (t, x)) x‖ ≤
              c₁ * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2,
      ⨆ x ∈ (SpatialLocalization.supportCylinder : Set ProblemStatement.Space),
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => BSum aB (t, x)) x‖ ≤
          (c₀ + c₁) * (1 - t) ^ (-β) :=
  rawJetsSplit_aB_of_twoSliceJets selectedDirectStages_smooth_physicalSublevel
    hjet0 hjet1

/-- **The rate bound from four summand envelopes.**  Feeding the two rows above
into `vorticityRateBound_aB_of_rawJets`, at the common constant
`c₀ + c₁ + d₀ + d₁`.  This is the first row on the frontier whose hypotheses are
one-sided per stage block: the initial stage and the positive-stage sum are
bounded separately, which is the format `CSPotentialSumEnvelope` and transport
T2 emit.  It discharges no hypothesis of its own — `VorticityRateBound (uSel aB)`
still rests on those four pointwise slice-jet bounds. -/
theorem vorticityRateBound_aB_of_splitJets
    {β : ℝ} {c₀ c₁ d₀ d₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hA0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedPotentialStages 0 (t, x)) x‖ ≤
              c₀ * (1 - t) ^ (-β))
    (hA1 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedPotentialStages) (t, x)) x‖ ≤
              c₁ * (1 - t) ^ (-β))
    (hB0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedDirectStages 0 (t, x)) x‖ ≤
              d₀ * (1 - t) ^ (-β))
    (hB1 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedDirectStages) (t, x)) x‖ ≤
              d₁ * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aB) := by
  have hc : 0 ≤ c₀ + c₁ + d₀ + d₁ := by linarith
  refine vorticityRateBound_aB_of_rawJets (β := β) hc ht₀ ?_ ?_
  · have h := rawJetsASum_of_splitJets hA0 hA1
    intro t ht k hk
    have hrp : 0 ≤ (1 - t) ^ (-β) :=
      Real.rpow_nonneg (by linarith [ht.1, ht.2] : (0 : ℝ) ≤ 1 - t) (-β)
    exact ((h t ht k hk).trans (mul_le_mul_of_nonneg_right (by linarith) hrp))
  · have h := rawJetsBSum_of_splitJets hB0 hB1
    intro t ht k hk
    have hrp : 0 ≤ (1 - t) ^ (-β) :=
      Real.rpow_nonneg (by linarith [ht.1, ht.2] : (0 : ℝ) ≤ 1 - t) (-β)
    exact ((h t ht k hk).trans (mul_le_mul_of_nonneg_right (by linarith) hrp))

/-! ## THE COMPOSER — two `CSPotentialSumEnvelope` envelopes give the rate bound

`vorticityRateBound_aB_of_splitJets` is the frontier's terminal row, but the two
positive-stage hypotheses `hA1`, `hB1` it asks for are *slice* estimates: jets of
`fun x => F (t, x)` on `{t} × Space`.  No producer in the repository proves a
slice estimate.  `CSPotentialSumEnvelope.potentialSum_negPower_envelope_physical`
and `potentialSum_negPower_envelope_of_cutBounds` emit the jets of the spacetime
function `F` itself, at spacetime points, in the negative-power form
`C · physicalQ h w ^ (-β)`.  The two rows below are the exact bridge: the base
converts from `physicalQ` to the remaining time by
`BKMProfileEnvelope.one_sub_le_physicalQ`, and the slice leg is
`BKMEnvCut.norm_iteratedFDeriv_slice_le` at the smoothness the P1 lane supplied
(`positivePotentialSum_aB_contDiffOn`, `positiveDirectSum_aB_contDiffOn`).  The
composer then asks transport T1 for two envelopes in the producer's own format
and transport T2 for the two stage-zero slice rows, and nothing else. -/

/-- **From spacetime jets to slice jets, strip-uniformly.**  Packaging
`BKMEnvCut.norm_iteratedFDeriv_slice_le` in the format both raw-envelope
consumers ask for: a pointwise bound on the jets of a spacetime function `F` on
the time strip `{t} × Space`, `t ∈ Ico t₀ 1`, transfers to the same bound on the
jets of the slices `fun x => F (t, x)`, with no change of constant or rate.  The
only input beyond the bound is `ContDiffOn ℝ ∞ F preterminal`. -/
private theorem sliceJetBound_of_spacetimeJetBound
    {F : ProblemStatement.SpaceTime → ProblemStatement.Space}
    (hF : ContDiffOn ℝ ∞ F PhysicalWaveSum.preterminal)
    {β : ℝ} {c : ℝ} {t₀ : ℝ}
    (h : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k F (t, x)‖ ≤ c * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space => F (t, x)) x‖ ≤
          c * (1 - t) ^ (-β) := by
  intro t ht k hk x
  exact (BKMEnvCut.norm_iteratedFDeriv_slice_le (f := F) PhysicalWaveSum.preterminal_open hF
    t (fun y => ht.2) x k).trans (h t ht k hk x)

/-- **Base transfer: a `physicalQ` envelope is a remaining-time envelope.**
`CSPotentialSumEnvelope`'s output is `C · physicalQ h w ^ (-β)` at spacetime
points `w`.  Since the similarity coordinate dominates the remaining time
(`BKMProfileEnvelope.one_sub_le_physicalQ: 1 - t ≤ physicalQ h (t, x)`, uniform
in `x`) and `r · ↦ r ^ (-β)` is antitone for `0 ≤ β`, every such envelope is
verbatim an envelope at the base `(1 - t) ^ (-β)` that the whole `BKMEnv*` chain
consumes, at the same constant and the same rate. -/
theorem negPowerEnvelope_to_stripJetBound
    {F : ProblemStatement.SpaceTime → ProblemStatement.Space}
    {β : ℝ} (hβ : 0 ≤ β) {C : ℝ} (hC : 0 ≤ C) {t₀ : ℝ}
    (henv : ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m F w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k F (t, x)‖ ≤ C * (1 - t) ^ (-β) := by
  intro t ht k hk x
  refine (henv k hk (t, x) ht.2).trans (mul_le_mul_of_nonneg_left ?_ hC)
  refine Real.rpow_le_rpow_of_nonpos (by linarith [ht.2] : (0 : ℝ) < 1 - t) ?_
    (by linarith)
  exact Navier.Analysis.BKMProfileEnvelope.one_sub_le_physicalQ
    outgoing.data.h_pos outgoing.data.h_lt_half ht.2 x

/-- **The composer: two spacetime envelopes and two stage-zero rows give the
rate bound.**  Its two positive-stage hypotheses `henvA`, `henvB` are stated in
exactly the conclusion format of
`CSPotentialSumEnvelope.potentialSum_negPower_envelope_of_cutBounds` /
`…_physical` at the ceiling `M = 2` over `S = PhysicalWaveSum.preterminal` — one
for the selected potential stages, one for the selected direct stages — so that
carrier needs no further packaging to feed this row; `BKMProfileEnvelope`'s
coordinate comparison converts the base and
`BKMEnvCut.norm_iteratedFDeriv_slice_le` converts spacetime jets to slice jets,
both at the same constant and rate.  The two remaining hypotheses are the
stage-zero slice rows `hjet0` of `rawJetsASum_of_splitJets` /
`rawJetsBSum_of_splitJets` in the format transport T2 emits them.  So
`VorticityRateBound (uSel aB)` now rests on exactly two named analytic inputs:
T1's positive-stage envelope with its side condition `hnum`, and T2's stage-zero
bound.  This row discharges neither. -/
theorem vorticityRateBound_aB_of_negPowerEnvelopes
    {β : ℝ} (hβ : 0 ≤ β)
    {c₀ c₁ d₀ d₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hA0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedPotentialStages 0 (t, x)) x‖ ≤
              c₀ * (1 - t) ^ (-β))
    (hB0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedDirectStages 0 (t, x)) x‖ ≤
              d₀ * (1 - t) ^ (-β))
    (henvA : ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedPotentialStages)) w‖ ≤
              c₁ * PhysicalWaveSum.physicalQ h w ^ (-β))
    (henvB : ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedDirectStages)) w‖ ≤
              d₁ * PhysicalWaveSum.physicalQ h w ^ (-β)) :
    VorticityRateBound (uSel aB) :=
  vorticityRateBound_aB_of_splitJets hc₀ hc₁ hd₀ hd₁ ht₀ hA0
    (sliceJetBound_of_spacetimeJetBound
      (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages
          ActualCandidateAssembly.selectedPotentialStages))
      positivePotentialSum_aB_contDiffOn
      (negPowerEnvelope_to_stripJetBound
        (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages
            ActualCandidateAssembly.selectedPotentialStages))
        (t₀ := t₀) hβ hc₁ henvA))
    hB0
    (sliceJetBound_of_spacetimeJetBound
      (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages
          ActualCandidateAssembly.selectedDirectStages))
      positiveDirectSum_aB_contDiffOn
      (negPowerEnvelope_to_stripJetBound
        (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
          (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages
            ActualCandidateAssembly.selectedDirectStages))
        (t₀ := t₀) hβ hd₁ henvB))

/-! ## Transport T1 instantiated at the actual schedule `aB`

Both envelope hypotheses of `vorticityRateBound_aB_of_negPowerEnvelopes` are
now produced at `aB`.  The `CSPotentialSumEnvelope` producer runs at
`U = S = CutStageEstimates.physicalSublevel h qbigSel`: there its per-stage
smoothness hypothesis `hA` is exactly the estimates record field
(`selectedPotentialStages_smooth_physicalSublevel` /
`selectedDirectStages_smooth_physicalSublevel`), its `CutStageBounds` input is
`aB_cutBounds` restricted to the sublevel, and its gain/loss functions are the
`aB_cutBounds` pair `(fun j => gainSel j / 2, lossSel)`.  The composer's
raw-stage smoothness gap on the envelope domain is closed not by new analysis
but by extending the conclusion pointwise from the open sublevel to ALL of
`PhysicalWaveSum.preterminal`: at a preterminal point `w` with
`qbigSel ≤ physicalQ h w` every cut stage has a zero germ
(`CutStageEstimates.cut_product_eventually_zero` fed by the scale gap
`aB_gap_mul`), all late stages vanish on a common neighbourhood
(`SolenoidalDiagonal.eventually_zero_tail`), so the diagonal `tsum` has a zero
germ and every jet at `w` is exactly `0`.  The producer `of_cutBounds` needs
one more input, `hnum`: the three gain-against-loss inequalities
`∀ m ≤ 2, 0 ≤ gainSel 1 / 2 - lossSel m`.  Unlike the gap closed above, this
one is not merely undischarged — `not_hnum_aB` below shows it is FALSE at the
selected estimates (by `Construction.HnumFalsification.not_hnum`), so no
schedule and no witness can ever feed this producer's `hnum` hypothesis at
ceiling `M = 2`.  The envelope rows that carried `hnum` as a hypothesis
(`negPowerEnvelope_aB_potential`, `negPowerEnvelope_aB_direct`,
`vorticityRateBound_aB_of_hnum_and_stageZero`) were therefore vacuous and are
removed; the live route is the `_free` chain built next from
`CS_PotentialSumEnvelopeGrowth`, which needs no such inequality. -/

open scoped BigOperators

/-- The schedule `aB` starts at `1` and grows, so every scale realisation is
`1 ≤ (aB j : ℝ)`: the admissibility input of the
`CSPotentialSumEnvelope` large-scale vanishing row. -/
private theorem aB_ge_one (j : ℕ) : (1 : ℝ) ≤ (aB j : ℝ) := by
  obtain ⟨hlower, _, _, ham, _, _, _, _⟩ := aB_selected
  exact_mod_cast hlower.trans (ham.monotone (Nat.zero_le j))

/-- The selected estimates gain is monotone (record field). -/
private theorem gainSel_mono : Monotone gainSel :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).gain_mono

/-- The selected estimates gain tends to infinity (record field). -/
private theorem gainSel_top : Tendsto gainSel atTop atTop :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).gain_top

/-- The selected estimates gain is strictly positive from stage one
(record field). -/
private theorem gainSel_pos (j : ℕ) (hj : 1 ≤ j) : (0 : ℝ) < gainSel j :=
  (ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold
    ActualCandidateConstruction.selectedThreshold_geometry).gain_pos j hj

/-- The `aB_cutBounds` gain function `fun j => gainSel j / 2` is monotone. -/
private theorem gainSel_half_mono : Monotone fun j => gainSel j / 2 := by
  intro i j hij
  show gainSel i * (2 : ℝ)⁻¹ ≤ gainSel j * (2 : ℝ)⁻¹
  exact mul_le_mul_of_nonneg_right (gainSel_mono hij)
    (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))

/-- The `aB_cutBounds` gain function tends to infinity. -/
private theorem gainSel_half_top : Tendsto (fun j => gainSel j / 2) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ?_
  obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp gainSel_top (2 * b)
  exact ⟨i, fun a hai => (le_div_iff₀ (by norm_num : (0 : ℝ) < (2 : ℝ))).mpr
    (by linarith [hi a hai])⟩

/-- The `aB_cutBounds` gain function is nonnegative from stage one. -/
private theorem gainSel_half_pos (j : ℕ) (hj : 1 ≤ j) : (0 : ℝ) ≤ gainSel j / 2 :=
  div_nonneg (gainSel_pos j hj).le (by norm_num : (0 : ℝ) ≤ 2)

/-- **The envelope instantiation at the selected schedule, per stage sequence.**
`CSPotentialSumEnvelope.potentialSum_negPower_envelope_of_cutBounds` at
`a := fun j => (aB j : ℝ)`, `q := physicalQ h`,
`U = S := physicalSublevel h qbigSel` (open by `physicalSublevel_open`),
ceiling `M = 2`, gain/loss `aB_cutBounds`'s own pair — then the pointwise
extension of its conclusion from the sublevel to all of `preterminal` through
the germ-zero rows, verbatim the mechanism of
`CutStageEstimates.exists_physical_local_diagonal_cut_bounds` at a point
outside the sublevel.  At the ceiling `M = 2` the producer's `hnum` ranges
over the single stage `j = 1` and orders `m ≤ 2`, so the concrete three-line
`hnum` hypothesis feeds it. -/
private theorem negPowerEnvelope_aB_extend
    {A : ℕ → ProblemStatement.VelocityField}
    (hex : ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ 2,
      ∀ w ∈ CutStageEstimates.physicalSublevel h qbigSel,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w‖ ≤
            C * PhysicalWaveSum.physicalQ h w ^ (-β)) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w‖ ≤
            C * PhysicalWaveSum.physicalQ h w ^ (-β) := by
  obtain ⟨C, β, hC, hβ, hsub⟩ := hex
  refine ⟨C, β, hC, hβ, ?_⟩
  intro m hm w hw
  by_cases hu : w ∈ CutStageEstimates.physicalSublevel h qbigSel
  · exact hsub m hm w hu
  · have hlarge : qbigSel ≤ PhysicalWaveSum.physicalQ h w :=
      le_of_not_gt fun hs => hu ⟨hw, hs⟩
    obtain ⟨N, hzero⟩ :=
      SolenoidalDiagonal.eventually_zero_tail aB_tendsto_real
        (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
          outgoing.data.h_lt_half hw).continuousAt
        (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw)
        (CutStageEstimates.positiveStages A)
    have hsmall : ∀ᶠ y in 𝓝 w,
        ∀ j ∈ Finset.range N,
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) j y = 0 := by
      refine (eventually_all_finset (I := Finset.range N)).mpr fun j _hj => ?_
      exact CutStageEstimates.cut_product_eventually_zero
        (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
          outgoing.data.h_lt_half hw).continuousAt
        (CutStageEstimates.positiveStages A j) (aB j)
        ((aB_gap_mul j).trans_le
          (mul_le_mul_of_nonneg_left hlarge (aB_pos_real j).le))
    have hgerms : (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) =ᶠ[𝓝 w]
        (fun _ : ProblemStatement.SpaceTime => (0 : ProblemStatement.Space)) := by
      filter_upwards [hsmall, hzero] with y hy1 hy2
      show (∑' j : ℕ, SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ))
          (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A) j y) = 0
      have hterm : ∀ j : ℕ,
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) j y = 0 := by
        intro j
        rcases Nat.lt_or_ge j N with hj | hj
        · exact hy1 j (Finset.mem_range.mpr hj)
        · exact hy2 j hj
      rw [tsum_congr hterm, tsum_zero]
    have hjet : iteratedFDeriv ℝ m (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w =
        iteratedFDeriv ℝ m (fun _ : ProblemStatement.SpaceTime =>
          (0 : ProblemStatement.Space)) w :=
      (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hgerms m).self_of_nhds
    rw [hjet, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (le_of_lt hC)
      (Real.rpow_nonneg (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos
        outgoing.data.h_lt_half hw).le _)

/-- **The envelope per stage sequence with NO `hnum`.**  The sublevel envelope
is produced by `CSPotentialSumEnvelopeGrowth.potentialSum_negPower_envelope_of_cutBounds_free`
and extended to all of `preterminal` by `negPowerEnvelope_aB_extend`:
the low stage `j = 1` is allowed to grow like a negative power of
`physicalQ h`, so the gain-against-loss inequality that
`Construction.HnumFalsification` proves false at this witness is not needed. -/
private theorem negPowerEnvelope_aB_preterminal_free
    {A : ℕ → ProblemStatement.VelocityField}
    (hAsub : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbigSel))
    (hBsub : DiagonalJetBounds.CutStageBounds (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) A (fun j => gainSel j / 2) lossSel
      (CutStageEstimates.physicalSublevel h qbigSel)) :
    ∃ C β : ℝ, 0 < C ∧ 0 ≤ β ∧ ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w‖ ≤
            C * PhysicalWaveSum.physicalQ h w ^ (-β) :=
  negPowerEnvelope_aB_extend
    (CSPotentialSumEnvelopeGrowth.potentialSum_negPower_envelope_of_cutBounds_free
      (a := fun j => (aB j : ℝ))
      aB_tendsto_real (fun j => aB_ge_one j)
      (q := PhysicalWaveSum.physicalQ h)
      (U := CutStageEstimates.physicalSublevel h qbigSel)
      (S := CutStageEstimates.physicalSublevel h qbigSel)
      (CutStageEstimates.physicalSublevel_open outgoing.data.h_pos
        outgoing.data.h_lt_half qbigSel)
      (Subset.refl _)
      (physicalQ_contDiffOn_preterminal.mono Set.inter_subset_left)
      (fun _x hx => PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos
        outgoing.data.h_lt_half hx.1)
      (fun _j _hj => hAsub _j)
      (g := fun j => gainSel j / 2) (L := lossSel)
      gainSel_half_mono gainSel_half_top gainSel_half_pos
      (CutStageEstimates.positiveStages_cut_bounds hBsub)
      2
      (fun _j _hj hjm => by omega))

/-- **T1 at the selected potential stages, unconditionally.** -/
theorem negPowerEnvelope_aB_potential_free :
    ∃ c₁ β : ℝ, 0 < c₁ ∧ 0 ≤ β ∧ ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedPotentialStages)) w‖ ≤
              c₁ * PhysicalWaveSum.physicalQ h w ^ (-β) :=
  negPowerEnvelope_aB_preterminal_free selectedPotentialStages_smooth_physicalSublevel
    (fun j hj m hm x hx => (aB_cutBounds).potential j hj m hm x hx.1)

/-- **T1 at the selected direct stages, unconditionally.** -/
theorem negPowerEnvelope_aB_direct_free :
    ∃ d₁ β : ℝ, 0 < d₁ ∧ 0 ≤ β ∧ ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m
          (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
            (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages
              ActualCandidateAssembly.selectedDirectStages)) w‖ ≤
              d₁ * PhysicalWaveSum.physicalQ h w ^ (-β) :=
  negPowerEnvelope_aB_preterminal_free selectedDirectStages_smooth_physicalSublevel
    (fun j hj m hm x hx => (aB_cutBounds).direct j hj m hm x hx.1)

/-- Off the sublevel `physicalQ h > 1` every `aB` diagonal sum has a zero
germ: the jets are exactly `0`, at every order, uniformly in the stage
sequence.  This is what lets a `physicalQ` envelope be repointed to a larger
rate without changing its constant. -/
private theorem aB_potentialSum_vanishing {A : ℕ → ProblemStatement.VelocityField}
    (m : ℕ) {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    (hgt : (1 : ℝ) < PhysicalWaveSum.physicalQ h w) :
    iteratedFDeriv ℝ m (SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
      (PhysicalWaveSum.physicalQ h) (CutStageEstimates.positiveStages A)) w = 0 :=
  CSPotentialSumEnvelope.potentialSum_large_scale_vanishing_sub
    (a := fun j => (aB j : ℝ)) aB_ge_one
    (q := PhysicalWaveSum.physicalQ h)
    (U := PhysicalWaveSum.preterminal) (S := PhysicalWaveSum.preterminal)
    PhysicalWaveSum.preterminal_open (Subset.refl _)
    (fun _x hx => (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
      outgoing.data.h_lt_half hx).contDiffWithinAt)
    w hw hgt m

/-- **Raising the rate never breaks a spacetime negative-power envelope for
the diagonal sum.**  On `physicalQ h ≤ 1` the antitone power comparison turns
`C · q ^ (-β)` into `C · q ^ (-β')` for `β ≤ β'`; above `1` the jets vanish by
`aB_potentialSum_vanishing` and the inequality is free.  Same constant. -/
private theorem negPowerEnvelope_exponent_le
    {F : ProblemStatement.SpaceTime → ProblemStatement.Space} {C : ℝ} (hC : 0 ≤ C)
    {β β' : ℝ} (hββ : β ≤ β')
    (hvan : ∀ m : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
        (1 : ℝ) < PhysicalWaveSum.physicalQ h w → iteratedFDeriv ℝ m F w = 0)
    (henv : ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m F w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (-β)) :
    ∀ m ≤ 2, ∀ w ∈ PhysicalWaveSum.preterminal,
        ‖iteratedFDeriv ℝ m F w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (-β') := by
  intro m hm w hw
  by_cases hgt : (1 : ℝ) < PhysicalWaveSum.physicalQ h w
  · rw [hvan m w hw hgt, norm_zero]
    exact mul_nonneg hC
      (Real.rpow_nonneg (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos
        outgoing.data.h_lt_half hw).le _)
  · have hq1 : PhysicalWaveSum.physicalQ h w ≤ 1 := le_of_not_gt hgt
    exact (henv m hm w hw).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge
        (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw)
        hq1 (by linarith [hββ] : (-β' : ℝ) ≤ -β)) hC)

/-- Raising the rate never breaks the remaining-time base on the strip:
`0 < 1 - t ≤ 1` for `t ∈ Ico t₀ 1 ⊆ Ico (3/4) 1`. -/
private theorem sliceBase_exponent_le {c : ℝ} (hc : 0 ≤ c)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    {β β' : ℝ} (hββ : β ≤ β') {t : ℝ} (ht : t ∈ Ico t₀ (1 : ℝ)) :
    c * (1 - t) ^ (-β) ≤ c * (1 - t) ^ (-β') :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (by linarith [ht.2] : (0 : ℝ) < 1 - t)
      (by linarith [ht.1, ht₀.1] : 1 - t ≤ 1) (by linarith [hββ] : (-β' : ℝ) ≤ -β)) hc

/-- **Near-terminal assembly at the actual schedule.**
`VorticityRateBound (uSel aB)` from the two transport-T2 stage-zero slice rows
ALONE.  This is the `hnum`-conditioned assembly this file used to state twice —
once carrying `∀ m ≤ 2, 0 ≤ gainSel 1 / 2 - lossSel m` as a hypothesis, once
without it — collapsed to one after `not_hnum_aB` showed the hypothesis is
false at the selected estimates, so the conditioned row was vacuous and added
nothing the unconditioned row lacks.  Both composer envelopes come from the
`_free` producers; the two spacetime envelopes and the two slice rows are
repointed to the common rate `max β₀ (max βA βB)` at their own constants
(enlarging the rate is free where the jets vanish and monotone where
`physicalQ h ≤ 1`, `1 - t ≤ 1`), and the composer finishes.  The two
stage-zero rows are the transport-T2 residual. -/
theorem vorticityRateBound_aB_of_stageZero
    {β₀ : ℝ} {c₀ d₀ : ℝ} (hc₀ : 0 ≤ c₀) (hd₀ : 0 ≤ d₀)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hA0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedPotentialStages 0 (t, x)) x‖ ≤
              c₀ * (1 - t) ^ (-β₀))
    (hB0 : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ∀ x : ProblemStatement.Space,
        ‖iteratedFDeriv ℝ k (fun x : ProblemStatement.Space =>
          SolenoidalDiagonal.cutStage (fun j => (aB j : ℝ)) (PhysicalWaveSum.physicalQ h)
            ActualCandidateAssembly.selectedDirectStages 0 (t, x)) x‖ ≤
              d₀ * (1 - t) ^ (-β₀)) :
    VorticityRateBound (uSel aB) := by
  obtain ⟨c₁, βA, hc₁, hβA, henvA⟩ := negPowerEnvelope_aB_potential_free
  obtain ⟨d₁, βB, hd₁, hβB, henvB⟩ := negPowerEnvelope_aB_direct_free
  let β := max β₀ (max βA βB)
  have hβ : (0 : ℝ) ≤ β :=
    hβA.trans ((le_max_left βA βB).trans (le_max_right β₀ (max βA βB)))
  refine vorticityRateBound_aB_of_negPowerEnvelopes (β := β) hβ (hc₀ := hc₀)
    (hc₁ := le_of_lt hc₁) (hd₀ := hd₀) (hd₁ := le_of_lt hd₁) (ht₀ := ht₀)
    (fun t ht k hk x => (hA0 t ht k hk x).trans
      (sliceBase_exponent_le hc₀ ht₀ (le_max_left β₀ (max βA βB)) ht))
    (fun t ht k hk x => (hB0 t ht k hk x).trans
      (sliceBase_exponent_le hd₀ ht₀ (le_max_left β₀ (max βA βB)) ht))
    (negPowerEnvelope_exponent_le
      (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages
          ActualCandidateAssembly.selectedPotentialStages))
      (le_of_lt hc₁) ((le_max_left βA βB).trans (le_max_right β₀ (max βA βB)))
      (fun m _w hw hgt => aB_potentialSum_vanishing m hw hgt) henvA)
    (negPowerEnvelope_exponent_le
      (F := SolenoidalDiagonal.potentialSum (fun j => (aB j : ℝ))
        (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages
          ActualCandidateAssembly.selectedDirectStages))
      (le_of_lt hd₁) ((le_max_right βA βB).trans (le_max_right β₀ (max βA βB)))
      (fun m _w hw hgt => aB_potentialSum_vanishing m hw hgt) henvB)

end Navier.Analysis.BKMEnvBoundedSchedule

#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_selected
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.not_hnum_aB
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_cutBounds
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_candidate
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.uSel_aB_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.ASum_aB_slice_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.BSum_aB_slice_smooth
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.polyUpper_aB_of_cylSums
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_cylSums
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_rawJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.zero_mem_cylB
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.cylBSup_le
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.rawJetsASum_of_spaceJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.rawJetsBSum_of_spaceJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_spaceJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.nat_le_infty
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.selectedPotentialStages_smooth_physicalSublevel
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.selectedDirectStages_smooth_physicalSublevel
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_strictMono
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_tendsto_real
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_pos_real
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_scale_gap
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_gap_mul
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.physicalQ_contDiffOn_preterminal
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.cutStage_aB_contDiffOn
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.positiveSum_aB_contDiffAt
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.positiveSum_aB_contDiffOn
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.positivePotentialSum_aB_contDiffOn
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.positiveDirectSum_aB_contDiffOn
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.iteratedFDeriv_potentialSum_aB_split
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.iteratedFDeriv_ASum_aB_split
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.iteratedFDeriv_BSum_aB_split
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.norm_potentialSum_aB_le_split
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.rawJetsSplit_aB_of_twoSliceJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.rawJetsASum_of_splitJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.rawJetsBSum_of_splitJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_splitJets
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.sliceJetBound_of_spacetimeJetBound
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.negPowerEnvelope_to_stripJetBound
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_negPowerEnvelopes
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_ge_one
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_mono
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_top
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_pos
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_half_mono
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_half_top
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.gainSel_half_pos
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.aB_potentialSum_vanishing
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.negPowerEnvelope_exponent_le
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.sliceBase_exponent_le
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.negPowerEnvelope_aB_potential_free
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.negPowerEnvelope_aB_direct_free
#print axioms Navier.Analysis.BKMEnvBoundedSchedule.vorticityRateBound_aB_of_stageZero
