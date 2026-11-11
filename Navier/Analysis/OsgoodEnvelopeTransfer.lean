import Mathlib
import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.EnvelopePropagation

/-!
# The two envelope legs `CrownBridgeReduction` §4 consumes, and an obstruction

`Navier/Analysis/CrownBridgeReduction.lean:416` holds the repository's last
direct `sorry`: `horizonLocal_of_osgoodEnvelopeMajorant`, whose goal is
`HorizonLocalCriticalControl h3EnvelopeControl` from `OsgoodEnvelopeMajorant`.
This file certifies the envelope-side step that leg needs and records an
obstruction the crown header has not yet recorded.  It edits no crown file and
rests no result on §4's conclusion.

**The horizon transfer (certified here).**  `OsgoodEnvelopeMajorant`'s barrier
covers `h3EnvelopeControl t u` for `t ∈ (0,T)` only, while the consumer's
conclusion is at `t = T`.  Because `h3EnvelopeControl T u` is a supremum over the
HALF-OPEN strip `Ico 0 T`, every slice `a ∈ Ico 0 T` is carried by the strictly
later interior time `a' = (a+T)/2`, so an interior bound closes the horizon with
no limit argument and no `toReal` round trip.  That is
`h3EnvelopeControl_le_coe_of_interior`, on the existing slice-carry leaf
`EnvelopePropagation.h3EnvelopeBudget_le_control`.

**The other leg** — turning the crown's divergence hypothesis into the uniform
`∃ M` cap — is certified in `Navier/Analysis/OsgoodDivergenceBridge.lean`
(this wave), which lands the bridge `OsgoodUniformBound` (`25d4018`) recorded as
not certified there.

**The obstruction (certified here).**  `OsgoodEnvelopeMajorant` guards its
barrier by two side conditions the CONSUMER must prove for each solution:
`ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T)` and the
matching `MonotoneOn`.  The crown header records that continuity as an open
producer obligation ("the slice continuity `t ↦ u t` is a producer obligation"),
and `EnvelopePropagation`'s rung P1 (`EnvelopeBudgetContinuousOn`) says the same
about the budget map.  This file proves the obligation is strictly harder than
P1: `h3EnvelopeControl 0 u = 0` because the strip `Ico 0 0` is empty, while every
strictly positive time carries the WHOLE datum budget,
`h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u` because `0 ∈ Ico 0 t`.  So,
assuming only the finiteness rung P0 on the control inside the horizon (needed
because `ENNReal.toReal ⊤ = 0` would otherwise silently discard the datum — the
very failure mode the crown's design note flags), continuity on `[0, T]` forces
`(h3EnvelopeBudget (u 0)).toReal = 0`.  `EnvelopeDatumSeed.envelopeBudget_datumSeed`
and `EnvelopePropagation.envelopeBudget_init_eq_datumWeight` pin that budget to
the datum's own weight, so for any datum of positive `H³` envelope the side
condition of `OsgoodEnvelopeMajorant` AS WRITTEN cannot be discharged by any
P1-strength producer.  What §4 needs before the two certified legs above can be
consumed is a statement-level repair on the envelope side — a right-continuity
form, an `Icc δ T` form, or a control whose strip includes its left endpoint —
and that repair belongs to the file's owner, not to this lane.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal Topology MeasureTheory
open Set Filter MeasureTheory
open Navier Navier.Analysis Navier.Analysis.HorizonFreeBudgetRestart

namespace Navier.Analysis.OsgoodEnvelopeTransfer

/-- The envelope control at horizon `0` is `0`: the strip `Ico 0 0` is empty. -/
theorem h3EnvelopeControl_zero (u : VelocityEvolution) : h3EnvelopeControl 0 u = 0 := by
  unfold h3EnvelopeControl
  rw [Ico_self]
  simp

/-- **The horizon transfer.**  An interior bound of the envelope control by
`ENNReal.ofReal` of a value capped at `M : NNReal` extends to the horizon `T`
itself as `h3EnvelopeControl T u ≤ (M : ℝ≥0∞)` — the conclusion shape
`HorizonLocalCriticalControl` asks for.  No continuity and no limit at `T` is
used, so no finiteness guard appears. -/
theorem h3EnvelopeControl_le_coe_of_interior {u : VelocityEvolution} {T : ℝ} {M : NNReal}
    (hT : 0 < T)
    (hint : ∀ t ∈ Ioo (0 : ℝ) T, h3EnvelopeControl t u ≤ ENNReal.ofReal (↑M)) :
    h3EnvelopeControl T u ≤ (M : ℝ≥0∞) := by
  refine iSup_le fun a => iSup_le fun ha => ?_
  set a' : ℝ := (a + T) / 2 with ha'def
  have ha' : a' ∈ Ioo (0 : ℝ) T := by
    rw [ha'def]
    constructor
    · linarith [ha.1, hT]
    · linarith [ha.2]
  have ham : a ∈ Ico (0 : ℝ) a' := by
    rw [ha'def]
    exact ⟨ha.1, by linarith [ha.2]⟩
  calc h3EnvelopeBudget (u a) ≤ h3EnvelopeControl a' u :=
      EnvelopePropagation.h3EnvelopeBudget_le_control u ham
    _ ≤ ENNReal.ofReal (↑M) := hint a' ha'
    _ = (M : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- **The continuity obstruction.**  If the envelope control is finite inside the
horizon (the control-side form of rung P0) and the datum carries a positive
envelope budget, then `t ↦ (h3EnvelopeControl t u).toReal` is NOT continuous on
`[0, T]`: it is `0` at `t = 0` (`h3EnvelopeControl_zero`) and at least the datum
budget at every strictly positive time
(`EnvelopePropagation.h3EnvelopeBudget_le_control` at `0 ∈ Ico 0 t`), so it jumps at the left
endpoint of the interval on which `OsgoodEnvelopeMajorant` asks for continuity.
This is measured with a sequence inside `(0,T)` decreasing to `0`, so it uses no
`toReal` continuity and no finiteness beyond P0. -/
theorem not_continuousOn_envelopeControl_toReal_of_positive_budget
    {u : VelocityEvolution} {T : ℝ} (hT : 0 < T)
    (hfin : ∀ t ∈ Ioo (0 : ℝ) T, h3EnvelopeControl t u < ⊤)
    (hb0 : 0 < (h3EnvelopeBudget (u 0)).toReal) :
    ¬ ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Icc (0 : ℝ) T) := by
  intro hcont
  have hc := hcont.continuousWithinAt (left_mem_Icc.mpr hT.le)
  -- the datum budget is finite: otherwise `ENNReal.toReal ⊤ = 0` kills `hb0`
  have hne : h3EnvelopeBudget (u 0) ≠ ⊤ := by
    intro hh
    rw [hh] at hb0
    have htop : (⊤ : ℝ≥0∞).toReal = 0 := by simp
    rw [htop] at hb0
    exact lt_irrefl (0 : ℝ) hb0
  -- every strictly positive time carries the whole datum budget
  have hge : ∀ t ∈ Ioo (0 : ℝ) T,
      (h3EnvelopeBudget (u 0)).toReal ≤ (h3EnvelopeControl t u).toReal := by
    intro t ht
    refine (ENNReal.toReal_le_toReal hne (ne_of_lt (hfin t ht))).mpr ?_
    exact EnvelopePropagation.h3EnvelopeBudget_le_control u
      (Set.mem_Ico.mpr ⟨le_refl 0, ht.1⟩)
  -- a sequence inside `(0,T)` decreasing to the left endpoint
  have hden : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have htin : ∀ k : ℕ, T / ((k : ℝ) + 2) ∈ Ioo (0 : ℝ) T := by
    intro k
    refine ⟨div_pos hT (hden k), div_lt_self hT (by linarith [hden k])⟩
  have hrange : ∀ k : ℕ, T / ((k : ℝ) + 2) ∈ Icc (0 : ℝ) T := fun k =>
    ⟨le_of_lt (htin k).1, (htin k).2.le⟩
  have htend : Tendsto (fun k : ℕ => T / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine tendsto_atTop_atTop.mpr (fun b => ⟨Nat.ceil b + 1, fun n hn => ?_⟩)
    have hc1 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have hc2 : (Nat.ceil b : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the continuity at `0` tested along that sequence
  have hcT : Tendsto (fun t => (h3EnvelopeControl t u).toReal) (𝓝[Icc (0 : ℝ) T] 0)
      (𝓝 ((fun t => (h3EnvelopeControl t u).toReal) (0 : ℝ))) := hc
  have htW : Tendsto (fun k : ℕ => T / ((k : ℝ) + 2)) atTop (𝓝[Icc (0 : ℝ) T] 0) :=
    le_inf htend (tendsto_principal.mpr (Filter.Eventually.of_forall hrange))
  have hseq : Tendsto (fun k : ℕ => (h3EnvelopeControl (T / ((k : ℝ) + 2)) u).toReal)
      atTop (𝓝 ((fun t => (h3EnvelopeControl t u).toReal) (0 : ℝ))) := hcT.comp htW
  have hbl : ∀ k : ℕ, (h3EnvelopeBudget (u 0)).toReal ≤
      (h3EnvelopeControl (T / ((k : ℝ) + 2)) u).toReal := fun k => hge _ (htin k)
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hseq hbl
  have hz : (fun t => (h3EnvelopeControl t u).toReal) (0 : ℝ) = 0 := by
    show (h3EnvelopeControl (0 : ℝ) u).toReal = 0
    rw [h3EnvelopeControl_zero u]
    simp
  rw [hz] at hle
  linarith [hle, hb0]

end Navier.Analysis.OsgoodEnvelopeTransfer

#print axioms Navier.Analysis.OsgoodEnvelopeTransfer.h3EnvelopeControl_zero
#print axioms Navier.Analysis.OsgoodEnvelopeTransfer.h3EnvelopeControl_le_coe_of_interior
#print axioms Navier.Analysis.OsgoodEnvelopeTransfer.not_continuousOn_envelopeControl_toReal_of_positive_budget
