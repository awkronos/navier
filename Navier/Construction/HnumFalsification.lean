/-
Lane MSW-NAVIER-HNUM-1114 (campaign MATH-SWARM-1114, 2026-11-19).

`hnum` — the hypothesis `∀ m ≤ 2, 0 ≤ gainSel 1 / 2 - lossSel m` carried by
`Navier.Analysis.BKMEnvBoundedSchedule` — cannot be made a proof field of the
estimates witness, because at the witness it is FALSE.  The premise that no
numerals exist behind `Classical.choose` is wrong for this inequality: the
choose appears only in the constant fields (`potentialConstant` etc.) and in
the schedule `aB`; the three functions entering `hnum` are all explicit:

* `gainSel = (ActualCandidateAssembly.estimates B N0 hN).gain =
  ActualIterationLedger.gain h`, so `gainSel 1 / 2 = h / 20`;
* `lossSel = MixedDiagonalSchedule.commonLoss` of the three loss fields, and
  `commonLoss L₁ L₂ L₃ m = cutLoss (commonRawLoss L₁ L₂ L₃) m =
  finiteBound (commonRawLoss L₁ L₂ L₃) m + m ≥ 1` for every choice of the
  losses, because `finiteBound f m = 1 + ∑ k ≤ m, |f k| ≥ 1`.

With `h = outgoing.data.h < 1 / 2` (the standing profile axiom
`outgoing.data.h_lt_half`), every instance of `hnum` fails strictly:
`gainSel 1 / 2 - lossSel m < 1 / 40 - 1 < 0`.  The inequality names no
schedule, so the failure holds uniformly over every admissible `aB` and over
every `B, N0`: it is a property of the analytic envelope of the actual
glued construction, and no strengthening of the witness structure can
inhabit it — `potential_bound` pins the jet exponents to
`gain h j - potentialLoss m` with `gain h j = h * j / 10`, so enlarging
`gain` would contradict the proved stage bounds themselves.

Consequence for the trunk: the composer-side instantiation
`negPowerEnvelope_aB_preterminal` at stage `j = 1` and ceiling `M = 2` can
never receive `hnum`; the envelope hypothesis it feeds must be re-derived at
a stage `j` with `gain h j / 2 ≥ lossSel m` (possible, since
`gainSel_top`), or the cut-bound side condition must be restructured.
-/

import Navier.Construction.ActualCandidateAssembly

noncomputable section

namespace Navier.Construction.HnumFalsification

open Navier.Construction
open Navier.Construction.CorrectionInitialization ActualPrimary

/-- At the selected estimates the gain is literally the ledger gain, so its
value at stage `1` is `h / 10`.  The identity is definitional: `estimates`
builds the record with `gain := ActualIterationLedger.gain h`, and `choose`
never enters this field. -/
theorem estimates_gain_eq (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    (ActualCandidateAssembly.estimates B N0 hN).gain = ActualIterationLedger.gain h :=
  rfl

/-- Half the selected gain at stage `1` is below `1`. -/
theorem gainSel_half_lt_one (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    (ActualCandidateAssembly.estimates B N0 hN).gain 1 / 2 < (1 : ℝ) := by
  rw [estimates_gain_eq B N0 hN]
  unfold ActualIterationLedger.gain
  rw [Nat.cast_one, mul_one, div_div]
  rw [show (10 : ℝ) * 2 = 20 by norm_num]
  refine (div_lt_one (by norm_num : (0 : ℝ) < 20)).mpr ?_
  exact outgoing.data.h_lt_half.trans (by norm_num : (1 / 2 : ℝ) < 20)

/-- The common cut loss is at least `1` at every order, for ANY raw losses:
`commonLoss LA LB LP m = finiteBound (commonRawLoss LA LB LP) m + m` and
`finiteBound f m ≥ 1` unconditionally. -/
theorem commonLoss_one_le (LA LB LP : ℕ → ℝ) (m : ℕ) :
    (1 : ℝ) ≤ MixedDiagonalSchedule.commonLoss LA LB LP m :=
  le_trans (CutStageEstimates.finiteBound_one_le _ m)
    (le_add_of_nonneg_right (Nat.cast_nonneg m))

/-- **The falsification inequality.**  For every admissible estimate record
and every derivative order, half the stage-`1` gain is strictly BELOW the
common loss: this is `hnum` with the strict opposite sign, uniformly (no
schedule `aB` appears anywhere in it). -/
theorem gainSel_half_lt_lossSel (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (m : ℕ) :
    (ActualCandidateAssembly.estimates B N0 hN).gain 1 / 2 <
      MixedDiagonalSchedule.commonLoss
        (ActualCandidateAssembly.estimates B N0 hN).potentialLoss
        (ActualCandidateAssembly.estimates B N0 hN).directLoss
        (ActualCandidateAssembly.estimates B N0 hN).pressureLoss m :=
  lt_of_lt_of_le (gainSel_half_lt_one B N0 hN)
    (commonLoss_one_le (ActualCandidateAssembly.estimates B N0 hN).potentialLoss
      (ActualCandidateAssembly.estimates B N0 hN).directLoss
      (ActualCandidateAssembly.estimates B N0 hN).pressureLoss m)

/-- **`hnum` is false at every estimates witness, with falsification
witness `m = 0`.**  The consumer statement
`∀ m ≤ 2, 0 ≤ gainSel 1 / 2 - lossSel m` is refutable for every `B`, `N0`;
it is therefore not a hypothesis any proof-field strengthening of the
estimates record can carry without contradicting `potential_bound`. -/
theorem not_hnum (B N0 : ℕ) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    ¬ (∀ m ≤ 2, (0 : ℝ) ≤
        (ActualCandidateAssembly.estimates B N0 hN).gain 1 / 2 -
          MixedDiagonalSchedule.commonLoss
            (ActualCandidateAssembly.estimates B N0 hN).potentialLoss
            (ActualCandidateAssembly.estimates B N0 hN).directLoss
            (ActualCandidateAssembly.estimates B N0 hN).pressureLoss m) := by
  intro hall
  have h0 := hall 0 (by omega)
  linarith [gainSel_half_lt_lossSel B N0 hN 0]

end Navier.Construction.HnumFalsification

#print axioms Navier.Construction.HnumFalsification.not_hnum
#print axioms Navier.Construction.HnumFalsification.gainSel_half_lt_lossSel
