/-
Repository-native module (lane MSW-NAVIER-1114, 2026-11-14). Not a vendored
slice: it has no upstream counterpart and is outside the construction drift pin.
-/
import Navier.Construction.ActualCandidateAssembly

/-!
# A selected schedule that keeps its cut-stage bounds

`MixedCandidateAssembly.StageEstimates.exists_schedule` obtains its schedule
from `MixedDiagonalResidual.exists_physical_schedule_residual_zero`, which also
returns `MixedDiagonalSchedule.ThreeCutBounds` for that schedule, and then
discards the bounds.  `MixedCandidateWitness.SelectedSchedule` therefore does
not record them, and a schedule obtained by `Classical.choose` from the
candidate witness carries no quantitative cut-stage estimate at all.

This module keeps the bounds.  It replays the two assembly steps for the same
finite-stage inputs and returns one schedule which is selected, satisfies the
three cut-stage bounds on the preterminal region, and whose activated periodic
fields have the candidate properties.  Nothing is assumed beyond the inputs of
the existing witness theorem.
-/

noncomputable section

namespace Navier.Construction.BoundedScheduleWitness

open Set Function Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open MixedCandidateAssembly (StageEstimates)
open scoped Topology ContDiff

/-- The schedule of `StageEstimates.exists_schedule`, with the cut-stage bounds
that the residual schedule theorem proves for it retained. -/
theorem exists_schedule_cutBounds {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => E.gain j / 2)
        (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
        PhysicalWaveSum.preterminal ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P) := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  exact MixedDiagonalResidual.exists_physical_schedule_residual_zero hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant
      E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual lower

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The finite-stage inputs of
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` give one
schedule that is selected, keeps the three cut-stage bounds, and whose
activated periodic fields have the candidate properties. -/
theorem exists_bounded_candidate_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages j))
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig
      (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension
        (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, GermCandidateAssembly.AxisZeroOn
      (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    let A := GermCandidateAssembly.potentialStages H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages
    ∃ a : ℕ → ℕ, MixedCandidateWitness.SelectedSchedule F.data.h qbig A B P a ∧
      MixedDiagonalSchedule.ThreeCutBounds a F.data.h A B P (fun j => E.gain j / 2)
        (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
        PhysicalWaveSum.preterminal ∧
      ∃ forcing : VelocityField,
        CandidateProperties
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
              (PhysicalWaveSum.physicalQ F.data.h) A)
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
              (PhysicalWaveSum.physicalQ F.data.h) B)))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
              (PhysicalWaveSum.physicalQ F.data.h) P))) forcing := by
  let A := GermCandidateAssembly.potentialStages H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages
  obtain ⟨a, hal, hap, had, ham, hat, hgap, hb, hs, hz⟩ :=
    exists_schedule_cutBounds E F.data.h_pos F.data.h_lt_half hqbig 1
  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  have ha0 : 0 < ar 0 := by
    dsimp [ar]
    exact_mod_cast hap 0
  have hamin (j : ℕ) : ar 0 ≤ ar j := by
    dsimp [ar]
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (A 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hInitial hx hxz (Classical.choice (TailGaugePotential.finalPotential_awayExtensions H v upper bandFloor x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hpInitial hx hxz (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions H v upper bandFloor).2 x hx))
    simp only [P]
    exact h
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (B 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((hDirect 0).eventually_zero F.data.h_pos F.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (A j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (P j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => simpa only [P, MixedCandidateAssembly.pressureStages_succ] using hpStages j
  have ea := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0 eA
  have eb := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) (fun j _ => hDirect j) hB0 eB
  have ep := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0 eP
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    F.data.h_pos F.data.h_lt_half D hat ha0 hamin (hgap 0)
  have haxis := GermCandidateAssembly.origin_blowup H v upper bandFloor hqbig initial stages D
    hInitialAxis hStagesAxis hat
  obtain ⟨forcing, hc, -⟩ := CandidateConsequences.mixed_exists_force_with_consequences
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis
  exact ⟨a, ⟨hal, hap, had, ham, hat, hgap, hs, hz⟩, hb, forcing, hc⟩

end ActualBase

open CorrectionInitialization.ActualPrimary in
/-- The actual candidate data give a selected schedule that keeps its three
cut-stage bounds on the preterminal region. -/
theorem actual_bounded_witness (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig B N0)
        (ActualCandidateAssembly.potentialStages B N0 hN)
        (ActualCandidateAssembly.directStages B N0 hN)
        (ActualCandidateAssembly.pressureStages B N0 hN) a ∧
      MixedDiagonalSchedule.ThreeCutBounds a h
        (ActualCandidateAssembly.potentialStages B N0 hN)
        (ActualCandidateAssembly.directStages B N0 hN)
        (ActualCandidateAssembly.pressureStages B N0 hN)
        (fun j => (ActualCandidateAssembly.estimates B N0 hN).gain j / 2)
        (MixedDiagonalSchedule.commonLoss
          (ActualCandidateAssembly.estimates B N0 hN).potentialLoss
          (ActualCandidateAssembly.estimates B N0 hN).directLoss
          (ActualCandidateAssembly.estimates B N0 hN).pressureLoss)
        PhysicalWaveSum.preterminal ∧
      ∃ forcing : VelocityField,
        CandidateProperties
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (ActualCandidateAssembly.potentialStages B N0 hN))
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (ActualCandidateAssembly.directStages B N0 hN))))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure
            (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
              (ActualCandidateAssembly.pressureStages B N0 hN)))) forcing :=
  exists_bounded_candidate_of_finite_stages certificate modulation upper B
    (ActualCandidateConstruction.qbig_pos B N0) (ActualCandidateAssembly.initialPotential B N0)
    (ActualCandidateAssembly.positivePotential B N0 hN)
    (ActualCandidateAssembly.directData B N0 hN) (ActualCandidateAssembly.initialPressure B N0)
    (ActualCandidateAssembly.positivePressure B N0 hN) (ActualCandidateAssembly.estimates B N0 hN)
    (ActualCandidateAssembly.initialPotential_support B N0)
    (ActualCandidateAssembly.positivePotential_support B N0 hN)
    (ActualCandidateAssembly.directStages_support B N0 hN)
    (ActualCandidateAssembly.initialPressure_support B N0)
    (ActualCandidateAssembly.positivePressure_support B N0 hN)
    (ActualCandidateAssembly.endpoints B N0 hN).potential
    (ActualCandidateAssembly.endpoints B N0 hN).direct
    (ActualCandidateAssembly.endpoints B N0 hN).pressure
    (ActualCandidateAssembly.initialPotential_axisZeroOn B N0)
    (ActualCandidateAssembly.positivePotential_axisZeroOn B N0 hN)

end Navier.Construction.BoundedScheduleWitness

#print axioms Navier.Construction.BoundedScheduleWitness.exists_schedule_cutBounds
#print axioms Navier.Construction.BoundedScheduleWitness.exists_bounded_candidate_of_finite_stages
#print axioms Navier.Construction.BoundedScheduleWitness.actual_bounded_witness
