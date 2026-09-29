import Navier.Analysis.AprioriCriticalControlQuantifiers
import Navier.Analysis.BealeKatoMajda

/-!
# The frozen control-N budget record (W31-N01)

Crown queue row **Whole-space Navier–Stokes**: the surviving candidate control
`bkmVorticityControl` of `AprioriCriticalControlQuantifiers` is non-degenerate as
a functional (`bkmVorticityControl_nondegenerate`, shear witness) and
`APrioriCriticalControl bkmVorticityControl` (the named leaf
`NSBKMUniformVorticityApriori`) is crown-strength by that module's own
conservation-of-difficulty note.  This module converts that leaf into a FROZEN
NUMERICAL BUDGET RECORD, following the induction-scales pattern (OpenAI
`NavierStokesAndEuler`, `EulerPacketInductionScales.Scales`): the record's fields
are ONLY numerical inequalities and one convergent series, and NO field assumes
existence of a solution, packet, or continuation object.  Every member-level
obligation is then stated against concrete numerics instead of a floating `∃ M`.

## Contents

* `ControlNRecord` — the record; `budget R := ∑' j, R.block j` is the frozen
  horizon-free bound, carried by a strictly positive summable block series.
* `recordAt` / `defaultRecord31` — the record is inhabited at every viscosity
  (default block series `(1/2)^(j+1)`, budget `= 1`).
* `budget_pos` / `defaultRecord31_nondegenerate` — non-degeneracy: every inhabited
  record has strictly positive budget and strictly positive block terms.
* `MemberBudget31` / `MemberAdmits31` / `memberAdmits_memberBudget` — the BKM
  budget statement for members of the `SolvesBefore` class, PROVED for members
  whose `BKMControl` rate integral sits under the record envelope.
* `defaultRecord31_zeroMember` — class pole guard: the canonical zero member
  (`solvesBefore_zero`, `BKMControl.controlZero`) satisfies the default record's
  envelope, so the statement is not posed against an uninhabited class.
* `Admits31` — the all-members proposition. NOT proven here for any record;
  `admits_all_aPriori_bkm` shows that admitting at every viscosity is exactly
  `APrioriCriticalControl bkmVorticityControl`, i.e. crown-strength.

## Non-claims

No `sorry`. Nothing here proves `Admits31 R` (or its failure) for any record `R`;
the producer gap of `AprioriCriticalControlQuantifiers` (no `BKMControl` producer
for the wide `SolvesBefore` class, no horizon-uniform estimate) is untouched.
The record's `initialControl` / `rateIntegralBound` numerics are ENVELOPES for a
supplied control; supplying one for a general member is the open brick.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace Navier.Analysis.ControlNRecord31

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.BealeKatoMajda

/-! ## The record -/

/-- **The frozen control-N budget record.**  Fields are numerical data with
numerical proofs only — one strictly positive summable block series and the two
envelope inequalities — and no field mentions a solution, pressure, packet, or
continuation object.  `series_tie` freezes the rate-integral envelope inside the
series, and `velocity_tie` freezes the `BKMControl.velocity_bounded`-style
envelope `Y₀ · e^G` inside the same series, so ONE convergent sum bounds both the
vorticity-integral quantity and the continuation velocity envelope. -/
structure ControlNRecord where
  /-- The viscosity the record is stated at. -/
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  /-- Envelope for the initial value of a supplied continuation control (`Y₀ ≥ 1`). -/
  initialControl : ℝ
  initialControl_ge_one : 1 ≤ initialControl
  /-- Horizon-free envelope for the improper rate integral `∫₀ᵗ rate` (`G ≥ 0`). -/
  rateIntegralBound : ℝ
  rateIntegralBound_nonneg : 0 ≤ rateIntegralBound
  /-- The convergent block series carrying the budget. -/
  block : ℕ → ℝ
  block_pos : ∀ j, 0 < block j
  block_summable : Summable block
  /-- Numerical ties: the series is at least the frozen envelopes. -/
  series_tie : rateIntegralBound ≤ ∑' j, block j
  velocity_tie : initialControl * Real.exp rateIntegralBound ≤ ∑' j, block j

/-- The frozen budget of a record: the value of its convergent series. -/
def budget (R : ControlNRecord) : ℝ := ∑' j, R.block j

/-! ## Inhabitation with explicit numerics -/

private def defaultBlock : ℕ → ℝ := fun j => ((1 : ℝ) / 2) ^ (j + 1)

private theorem defaultBlock_pos (j : ℕ) : 0 < defaultBlock j :=
  pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) _

private theorem defaultBlock_eq : defaultBlock = fun j => ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ j := by
  funext j
  show ((1 : ℝ) / 2) ^ (j + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j
  rw [pow_succ]
  ring

private theorem defaultBlock_summable : Summable defaultBlock := by
  rw [defaultBlock_eq]
  exact Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))

private theorem defaultBlock_tsum : ∑' j, defaultBlock j = (1 : ℝ) := by
  rw [defaultBlock_eq, tsum_mul_left, tsum_geometric_two]
  norm_num

/-- The record at any prescribed positive viscosity.  All other numerics are the
default frozen series, so `budget (recordAt ν hν) = 1` at every viscosity. -/
def recordAt (ν : ℝ) (hν : 0 < ν) : ControlNRecord where
  viscosity := ν
  viscosity_pos := hν
  initialControl := 1
  initialControl_ge_one := le_refl 1
  rateIntegralBound := 0
  rateIntegralBound_nonneg := le_refl 0
  block := defaultBlock
  block_pos := defaultBlock_pos
  block_summable := defaultBlock_summable
  series_tie := by rw [defaultBlock_tsum]; norm_num
  velocity_tie := by
    have hexp : Real.exp (0 : ℝ) = (1 : ℝ) := Real.exp_zero
    rw [defaultBlock_tsum, hexp]
    norm_num

/-- The default record: viscosity `1`. -/
def defaultRecord31 : ControlNRecord := recordAt 1 zero_lt_one

theorem defaultRecord31_budget : budget defaultRecord31 = (1 : ℝ) := defaultBlock_tsum

/-! ## Non-degeneracy -/

/-- **Every inhabited record has a strictly positive frozen budget**: the block
series is strictly positive termwise and summable, so its sum dominates the
positive first term.  The record shape therefore cannot collapse to the
degenerate zero-budget envelope. -/
theorem budget_pos (R : ControlNRecord) : 0 < budget R := by
  have hsum : Tendsto (fun n : ℕ => (Finset.range n).sum R.block) atTop (𝓝 (budget R)) :=
    R.block_summable.hasSum.tendsto_sum_nat
  have hge : ∀ᶠ (n : ℕ) in atTop, R.block 0 ≤ (Finset.range n).sum R.block := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    calc R.block 0 = (Finset.range 1).sum R.block := (Finset.sum_range_one _).symm
      _ ≤ (Finset.range n).sum R.block :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn)
          fun j _ _ => (R.block_pos j).le
  have hconst : Tendsto (fun _ : ℕ => R.block 0) atTop (𝓝 (R.block 0)) := tendsto_const_nhds
  exact lt_of_lt_of_le (R.block_pos 0)
    (le_of_tendsto_of_tendsto hconst hsum hge)

/-- **Non-degeneracy of the default record**: positive budget and strictly
positive block series (the functional-level non-degeneracy of the quantity
itself is `bkmVorticityControl_nondegenerate`, proved in
`AprioriCriticalControlQuantifiers`). -/
theorem defaultRecord31_nondegenerate :
    0 < budget defaultRecord31 ∧ ∀ j, 0 < defaultRecord31.block j :=
  ⟨budget_pos defaultRecord31, defaultBlock_pos⟩

/-! ## The per-member BKM budget statement -/

/-- **Member budget claim** for the record at horizon `T`: the member's improper
vorticity integral (`bkmVorticityControl`, the quantity frozen by this record)
sits under the frozen budget. -/
def MemberBudget31 (R : ControlNRecord) (T : ℝ) (u : VelocityEvolution) : Prop :=
  bkmVorticityControl T u ≤ ENNReal.ofReal (budget R)

/-- **Admissible member**: a `SolvesBefore` member at the record's viscosity
whose supplied `BKMControl` has all rate integrals under the record's frozen
`rateIntegralBound`.  The datum clause of the a-priori leaf is deliberately
absent: `bkmVorticityControl` ignores values off the closed sub-horizons of
`Ico 0 T` (null-set insensitivity), so the terminal-junk witness of
`AprioriCriticalControlQuantifiers` does not apply to it, and the member claim
is about the member, not about its datum. -/
def MemberAdmits31 (R : ControlNRecord) (T : ℝ) (u : VelocityEvolution)
    (p : PressureEvolution) : Prop :=
  SolvesBefore R.viscosity T u p ∧
    ∃ c : BKMControl u T,
      ∀ t ∈ Set.Ico (0 : ℝ) T, (∫ s in (0 : ℝ)..t, c.rate s) ≤ R.rateIntegralBound

/-- **The budget is paid by the record, not re-proved per member.**  For any
positive horizon, a `MemberAdmits31` member satisfies `MemberBudget31`: the repo
bootstrap bound `bkmVorticityControl_le_ofReal_BKMControl_bound` plus the record's
frozen monotone ties.  This is the per-`SolvesBefore`-member BKM budget statement
discharged for the bootstrap-carrying subclass. -/
theorem memberAdmits_memberBudget {R : ControlNRecord} {T : ℝ} (hT : 0 < T)
    {u : VelocityEvolution} {p : PressureEvolution} (h : MemberAdmits31 R T u p) :
    MemberBudget31 R T u := by
  obtain ⟨_, c, hB⟩ := h
  refine le_trans (bkmVorticityControl_le_ofReal_BKMControl_bound hT c hB) ?_
  exact ENNReal.ofReal_le_ofReal R.series_tie

/-- **Class pole guard.**  The canonical zero member — `solvesBefore_zero` at the
default viscosity, carrying `BKMControl.controlZero` with rate `≡ 0` — satisfies
the default record's `MemberAdmits31` envelope at every positive horizon, hence
its budget statement by `memberAdmits_memberBudget`.  The member claim is
therefore not posed against an uninhabited class, and the zero member's vorticity
control sits under the frozen default budget. -/
theorem defaultRecord31_zeroMember (T : ℝ) (hT : 0 < T) :
    MemberBudget31 defaultRecord31 T (fun _ _ => (0 : Space)) := by
  refine memberAdmits_memberBudget hT
    ⟨solvesBefore_zero defaultRecord31.viscosity T, BKMControl.controlZero T, ?_⟩
  intro t _
  show (∫ s in (0 : ℝ)..t, (BKMControl.controlZero T).rate s) ≤ (0 : ℝ)
  rw [show (BKMControl.controlZero T).rate = fun _ => (0 : ℝ) from rfl,
      intervalIntegral.integral_const, smul_zero]

/-- **Record admissibility**: EVERY `SolvesBefore` member of the record's
viscosity at every positive horizon satisfies the frozen budget claim — with no
`BKMControl` hypothesis, i.e. the producer obligation of
`AprioriCriticalControlQuantifiers` internalized against the record's numerics.
NOT proven here for any record. -/
def Admits31 (R : ControlNRecord) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (u : VelocityEvolution) (p : PressureEvolution),
    SolvesBefore R.viscosity T u p → MemberBudget31 R T u

/-- **The record shape is faithful to the leaf.**  Admitting at every positive
viscosity (each viscosity equipped with its `recordAt` numerics) yields
`APrioriCriticalControl bkmVorticityControl`, the named crown leaf
`NSBKMUniformVorticityApriori`: the frozen budget supplies the `∃ M` uniformly in
horizon, member, and datum.  By the cited conservation-of-difficulty note, proving
`Admits31 (recordAt ν hν)` for a single viscosity is crown-strength work; this
file claims only the conversion, in the direction that shows the record adds no
strength beyond the leaf. -/
theorem admits_all_aPriori_bkm
    (H : ∀ (ν : ℝ) (hν : 0 < ν), Admits31 (recordAt ν hν)) :
    APrioriCriticalControl bkmVorticityControl := by
  intro ν hν u₀ hD
  have hbudget : 0 ≤ budget (recordAt ν hν) := (budget_pos _).le
  refine ⟨⟨budget (recordAt ν hν), hbudget⟩, fun T hT u p _hmatch hsolve => ?_⟩
  have hmem : MemberBudget31 (recordAt ν hν) T u := H ν hν T hT u p hsolve
  rw [MemberBudget31, ENNReal.ofReal_eq_coe_nnreal hbudget] at hmem
  exact hmem

end Navier.Analysis.ControlNRecord31

#print axioms Navier.Analysis.ControlNRecord31.budget_pos
#print axioms Navier.Analysis.ControlNRecord31.defaultRecord31_nondegenerate
#print axioms Navier.Analysis.ControlNRecord31.memberAdmits_memberBudget
#print axioms Navier.Analysis.ControlNRecord31.defaultRecord31_zeroMember
#print axioms Navier.Analysis.ControlNRecord31.admits_all_aPriori_bkm
#check @Navier.Analysis.ControlNRecord31.Admits31
