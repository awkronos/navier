import Navier.Analysis.EnvelopePropagation
import Navier.Analysis.WienerDatumSmooth
import Navier.Analysis.WienerRestartLeaf
import Navier.Analysis.EnvelopeFourierUniqueness
import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.WienerSobolevL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The continuous `Rep`-family rung collapses to P0 ∧ P1, and its constructive
# replacement: the dominated `Rep`-family route — F-027, residual item 4

**Mission.**  The F-026 propagation board (`Navier/Analysis/EnvelopePropagation.lean`,
at 5d8b3847a on `rv7/f026-cont-1006`) enumerates its residual items and names
item 4 — "a continuous `Rep`-family of representers — the input to
`envelopeBudget_continuousOn_of_repFamily`: `∀ t ∈ Ico 0 T, Rep (u t) (a t)` with
`t ↦ ⨆ i, h3F (a t · i)` continuous" — as the rung that closes crown-premise
propagation through the §5 bridge. This module attacks exactly item 4 and lands its
**reduction**: the item as stated is not an independent analytic rung. Because
`h3EnvelopeBudget_eq_iSup` makes the weight map of ANY pointwise-`Rep` family equal,
slice by slice, to the budget map itself, the two conjuncts of item 4 are (a) slice
representability — which §1 shows is equivalent to rung P0 (`EnvelopeBudgetFiniteOn`,
the ⊤-guard never firing), using the new `Rep`-side finiteness rows that a `WDatum`
plus a.e. boundedness force every component `H³` weight below `⊤` — and (b)
continuity of the weight map — which by the same pointwise equality IS rung P1
(`EnvelopeBudgetContinuousOn`). §3 lands the equivalence
`EnvelopeRepFamilyRoute T u ↔ EnvelopeBudgetFiniteOn T u ∧ EnvelopeBudgetContinuousOn T u`
as a theorem: the §5 bridge, read through item 4, is a re-parametrization of the two
named rungs it feeds — supplying a "continuous `Rep`-family" is restating them.

**What is genuinely new and unconditional here.**  (§1)
`rep_h3F_component_lt_top` / `rep_budget_lt_top` — every component weight of every
representer is finite (the `(1+x)⁶ ≤ 64·(1+x⁶)` binomial squeeze against the
`WDatum.mom_coord` moments, closed under `Rep.bdd`), hence a representable slice has
finite budget and `h3EnvelopeBudget v < ⊤ ↔ ∃ a, Rep v a` — the ⊤-guard fires exactly
at non-representability (the F-026 P0 docstring's "i.e." made precise; previously
only the forward direction existed, `exists_rep_of_budget_lt_top`). (§2) The
evolution form: `EnvelopeBudgetFiniteOn T u ↔ ∃ family, ∀ t ∈ Ico 0 T, Rep (u t) (a t)`
— choice, no analytic content — and the transport from finite horizon control.
Also choice-invariance of the bridge input at family level (`repFamilyWeight_eqOn`:
any two pointwise-`Rep` families have the SAME weight map on `Ico 0 T`, both being
the budget map) and the converse of the §5 bridge
(`repFamilyWeight_continuousOn_of_budgetContinuousOn`: P1 forces the weight
continuity of EVERY pointwise-`Rep` family). (§3) The collapse theorem. (§4) The
dominated-continuity engine: filter dominated convergence
(`tendsto_integral_filter_of_dominated_convergence` along `𝓝[Ico 0 T] t₀`, whose
`IsCountablyGenerated` instance is the nhdsWithin one) upgrades a family that is
continuous in `t` at a.e. frequency and polynomially dominated by ONE integrable
envelope into exactly the bridge hypothesis — `h3F` is rewritten as `ENNReal.ofReal`
of a real Bochner integral (`h3F_eq_ofReal_integral`, via
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.ofReal_toReal`), real DCT gives
continuity of the integral map, `continuous_ofReal` lifts it, and the `Fin 3`
supremum is the binary-max chain (`iSup_fin_three`, `ContinuousOn.sup`). This engine
is what a construction must plug into; it is NOT a construction. (§5) The honest
carrier of item 4 as its own named `Prop`, `EnvelopeDominatedRepFamilyRoute`, with
both-rung consumption rows.

**What remains open.**  The construction of a dominated `Rep`-family from the
carrier `SolvesBefore` + `RegularOnCompacts` remains the named obligation of §5 —
the frequency-side analytic content is the same as P0's route (interior `Hˢ`
smoothing giving all Fourier moments, `WDatum`, pointwise inversion), and the F-026
residual item 2's parenthetical "(weighted-`L²` dominated convergence — the seed's
`h3F_lt_top_of_schwartz` domination is the same shape)" is exactly the hypothesis
shape the §4 engine now consumes. Falsification note: nothing refuted here — the
collapse is an equivalence, so a route past item 4 AS STATED would have to refute
P0 ∧ P1, and no counterexample to either is known on R-solutions. The F-027 caution
applies to the physical-side Schwartz variant (generically false, Brandolese's
`|x|⁻⁴`); the frequency-side statement survives because `Rep` asks smoothness-class
content only.

**Placement note.**  Downstream of `EnvelopePropagation` (itself downstream of the
seed chain), same namespace discipline as the seed and propagation modules: one
namespace for this module's own path.  STACKED on `rv7/f026-cont-1006 @ 5d8b3847a`
(not yet merged to `main` @ 7a7cb23; merge-base b411836): fold order F-026 first,
this branch on top.  Both sides touch `Navier.lean`; this adds one import line after
`EnvelopePropagation`, alphabetically before `FloatExpCrossover`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate BigOperators

namespace Navier.Analysis.EnvelopeRepFamily

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.EnvelopeFourierUniqueness
open Navier.Analysis.EnvelopePropagation

/-! ## 1. Representability forces finite weights: the ⊤-guard is exactly non-representability -/

/-- The binomial squeeze `(1 + x)⁶ ≤ 64·(1 + x⁶)` on `[0, ∞)`, the only numerical
input to `rep_h3F_component_lt_top`. -/
theorem one_add_pow_six_le (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 6 ≤ 64 * (1 + x ^ 6) := by
  rcases lt_or_ge x 1 with h | h
  · calc (1 + x) ^ 6 ≤ (2 : ℝ) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ ≤ 64 * (1 + x ^ 6) := by nlinarith [pow_nonneg hx 6]
  · calc (1 + x) ^ 6 ≤ (2 * x) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 64 * x ^ 6 := by ring
      _ ≤ 64 * (1 + x ^ 6) := by nlinarith [pow_nonneg hx 6]

/-- The same lifted to `ℝ≥0∞`: `ofReal ((1+x)⁶) ≤ 64 · (1 + ofReal (x⁶))`. -/
theorem ofReal_one_add_pow_six_le (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal ((1 + x) ^ 6) ≤ (64 : ℝ≥0∞) * (1 + ENNReal.ofReal (x ^ 6)) := by
  calc ENNReal.ofReal ((1 + x) ^ 6)
      ≤ ENNReal.ofReal (64 * (1 + x ^ 6)) := ENNReal.ofReal_le_ofReal (one_add_pow_six_le x hx)
    _ = ENNReal.ofReal (64 : ℝ) * ENNReal.ofReal (1 + x ^ 6) :=
        ENNReal.ofReal_mul (by positivity)
    _ = (64 : ℝ≥0∞) * (1 + ENNReal.ofReal (x ^ 6)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_cast

/-- **A representer has finite `H³` component weight.**  The `WDatum` moment
hypotheses give finiteness of `∫ ofReal(‖ξ‖ⁿ)·‖a ξ i‖ₑ` at every `n`; `Rep.bdd`
turns the square `‖a ξ i‖ₑ²` into `‖a ξ i‖ₑ · ofReal A`; the binomial squeeze at
`n = 6` and the `n = 0` moment close the integral. This is the `Rep`-side finiteness
row the F-026 board had only for Schwartz profiles (`h3F_lt_top_of_schwartz`). -/
theorem rep_h3F_component_lt_top {v : VelocityField} {a : ES → ComplexSpace}
    (ha : Rep v a) (i : Fin 3) : h3F (fun ξ => a ξ i) < ⊤ := by
  obtain ⟨hd, hex, _, _⟩ := ha
  obtain ⟨A, hA0, hbd⟩ := hex
  have hc : (64 : ℝ≥0∞) * ENNReal.ofReal A < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top 64))
      ENNReal.ofReal_lt_top
  have h0 : ∫⁻ ξ, ‖a ξ i‖ₑ ∂(volume : Measure ES) < ⊤ := by
    simpa [pow_zero] using lt_top_iff_ne_top.mpr (hd.mom_coord 0 i)
  have h6 : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 6) * ‖a ξ i‖ₑ ∂(volume : Measure ES) < ⊤ :=
    lt_top_iff_ne_top.mpr (hd.mom_coord 6 i)
  unfold h3F
  refine lt_of_le_of_lt
    (lintegral_mono_ae (g := fun ξ =>
      (64 : ℝ≥0∞) * ENNReal.ofReal A *
        (‖a ξ i‖ₑ + ENNReal.ofReal (‖ξ‖ ^ 6) * ‖a ξ i‖ₑ)) ?_) ?_
  · filter_upwards [hbd] with ξ hξ
    have hne : ‖a ξ i‖ₑ ≤ ENNReal.ofReal A := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hξ i)
    calc ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖a ξ i‖ₑ ^ 2
        = ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * (‖a ξ i‖ₑ * ‖a ξ i‖ₑ) := by rw [pow_two]
      _ ≤ ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * (ENNReal.ofReal A * ‖a ξ i‖ₑ) :=
          mul_le_mul' le_rfl (mul_le_mul' hne le_rfl)
      _ ≤ ((64 : ℝ≥0∞) * (1 + ENNReal.ofReal (‖ξ‖ ^ 6))) * (ENNReal.ofReal A * ‖a ξ i‖ₑ) :=
          mul_le_mul' (ofReal_one_add_pow_six_le _ (norm_nonneg ξ)) le_rfl
      _ = (64 : ℝ≥0∞) * ENNReal.ofReal A *
            (‖a ξ i‖ₑ + ENNReal.ofReal (‖ξ‖ ^ 6) * ‖a ξ i‖ₑ) := by
              simp only [mul_add, one_mul,
                mul_assoc, mul_comm, mul_left_comm]
  · rw [lintegral_const_mul' (64 * ENNReal.ofReal A)
      (fun ξ => ‖a ξ i‖ₑ + ENNReal.ofReal (‖ξ‖ ^ 6) * ‖a ξ i‖ₑ)
      (lt_top_iff_ne_top.mp hc)]
    refine ENNReal.mul_lt_top hc ?_
    have hf1 : AEMeasurable (fun ξ => ‖a ξ i‖ₑ) volume :=
      (aemeasurable_congr
        (ae_of_all volume fun ξ => (ofReal_norm (a ξ i)).symm)).mpr
        ((ENNReal.measurable_ofReal.comp
          ((continuous_norm.measurable).comp
            ((measurable_pi_apply i).comp hd.meas))).aemeasurable)
    rw [lintegral_add_left' hf1
      (fun ξ => ENNReal.ofReal (‖ξ‖ ^ 6) * ‖a ξ i‖ₑ)]
    exact ENNReal.add_lt_top.mpr ⟨h0, h6⟩

/-- **A representable slice has finite budget.**  The collapse
`h3EnvelopeBudget_eq_iSup` with ONE representer replaces the `⨆` over all
representers by its weight; finiteness is the binary-max chain. -/
theorem rep_budget_lt_top {v : VelocityField} {a : ES → ComplexSpace} (ha : Rep v a) :
    h3EnvelopeBudget v < ⊤ := by
  rw [h3EnvelopeBudget_eq_iSup ha, iSup_fin_three, max_lt_iff, max_lt_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact rep_h3F_component_lt_top ha 0
  · exact rep_h3F_component_lt_top ha 1
  · exact rep_h3F_component_lt_top ha 2

/-- **The exact ⊤-guard characterization.**  A slice has finite envelope budget if
and only if it carries a `Rep` representer.  This is the F-026 P0 docstring's
"i.e." (representability = the guard not firing) made a theorem; previously only
the forward direction existed (`exists_rep_of_budget_lt_top`). -/
theorem h3EnvelopeBudget_lt_top_iff_existsRep (v : VelocityField) :
    h3EnvelopeBudget v < ⊤ ↔ ∃ a : ES → ComplexSpace, Rep v a :=
  ⟨exists_rep_of_budget_lt_top, fun ⟨_, ha⟩ => rep_budget_lt_top ha⟩

/-! ## 2. The evolution form and the choice-invariance of the bridge input -/

/-- **Rung P0, family form.**  `EnvelopeBudgetFiniteOn T u` is equivalent to the
existence of a pointwise `Rep`-family along `Ico 0 T`.  Choice, applied slice by
slice — no analytic content. -/
theorem envelopeBudgetFiniteOn_iff_existsRepFamily (T : ℝ) (u : VelocityEvolution) :
    EnvelopeBudgetFiniteOn T u ↔
      ∃ a : ℝ → ES → ComplexSpace, ∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t) := by
  refine ⟨fun hP0 => ?_, fun ⟨a, ha⟩ t ht => rep_budget_lt_top (ha t ht)⟩
  classical
  have hex : ∀ t : ℝ, ∃ y : ES → ComplexSpace, (t ∈ Ico (0 : ℝ) T) → Rep (u t) y := by
    intro t
    by_cases ht : t ∈ Ico (0 : ℝ) T
    · obtain ⟨y, hy⟩ := exists_rep_of_budget_lt_top (hP0 t ht)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  choose a ha using hex
  exact ⟨a, fun t ht => ha t ht⟩

/-- Finite horizon control supplies a pointwise `Rep`-family on the whole interval —
the family-level companion of `exists_rep_of_control_lt_top`. -/
theorem repFamily_of_envelopeControl_lt_top {T : ℝ} (u : VelocityEvolution)
    (h : h3EnvelopeControl T u < ⊤) :
    ∃ a : ℝ → ES → ComplexSpace, ∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t) :=
  (envelopeBudgetFiniteOn_iff_existsRepFamily T u).mp
    fun _ ht => (h3EnvelopeBudget_le_control u ht).trans_lt h

/-- **Choice-invariance of the bridge input.**  Any two pointwise-`Rep`-families of
`u` on `Ico 0 T` have the SAME weight map there: both are the budget map, pointwise.
The family-side echo of `rep_component_ae_eq` ("`h3F` cannot see a representer other
than the a.e.-unique one") — at the family level it cannot see the family at all. -/
theorem repFamilyWeight_eqOn (T : ℝ) (u : VelocityEvolution)
    {a b : ℝ → ES → ComplexSpace}
    (ha : ∀ s ∈ Ico (0 : ℝ) T, Rep (u s) (a s))
    (hb : ∀ s ∈ Ico (0 : ℝ) T, Rep (u s) (b s)) :
    EqOn (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i))
      (fun t => ⨆ i : Fin 3, h3F (fun ξ => b t ξ i)) (Ico (0 : ℝ) T) := by
  intro t ht
  have h1 : (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i)) t
      = h3EnvelopeBudget (u t) := (envelopeBudget_eq_repFamilyWeight ha ht).symm
  have h2 : (fun t => ⨆ i : Fin 3, h3F (fun ξ => b t ξ i)) t
      = h3EnvelopeBudget (u t) := (envelopeBudget_eq_repFamilyWeight hb ht).symm
  exact h1.trans h2.symm

/-- **The converse of the F-026 §5 bridge.**  P1 forces the weight-map continuity of
EVERY pointwise-`Rep`-family — because each such map is the budget map.  Combined
with `envelopeBudget_continuousOn_of_repFamily` this is the equivalence of §3. -/
theorem repFamilyWeight_continuousOn_of_budgetContinuousOn (T : ℝ) (u : VelocityEvolution)
    {a : ℝ → ES → ComplexSpace}
    (ha : ∀ s ∈ Ico (0 : ℝ) T, Rep (u s) (a s))
    (hP1 : EnvelopeBudgetContinuousOn T u) :
    ContinuousOn (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i)) (Ico (0 : ℝ) T) :=
  hP1.congr fun _ ht => (envelopeBudget_eq_repFamilyWeight ha ht).symm

/-! ## 3. The collapse: item 4 as stated is rung P0 ∧ rung P1 -/

/-- **Item 4, stated exactly as the F-026 residual list writes it.**  A pointwise
`Rep`-family along the evolution whose weight map is continuous on `Ico 0 T`. -/
def EnvelopeRepFamilyRoute (T : ℝ) (u : VelocityEvolution) : Prop :=
  ∃ a : ℝ → ES → ComplexSpace, (∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t)) ∧
    ContinuousOn (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i)) (Ico (0 : ℝ) T)

/-- **The reduction of residual item 4 (the F-027 verdict, as a theorem).**  The
continuous-`Rep`-family rung — the named input to the F-026 §5 bridge — holds if and
only if P0 and P1 hold.  It is not an independent analytic rung: supplying the
family adds no content beyond the two named rungs the bridge feeds (the family
exists by choice from P0, and its weight continuity IS P1 by choice-invariance).
Hence the §5 bridge, read through item 4, is a re-parametrization of P1 and P0, not
a decomposition — the genuine constructive content is the dominated route of §4–§5.
Docstring verdict for the residual list: item 4, as literally stated, DECOMPOSES to
P0 ∧ P1. -/
theorem envelopeRepFamilyRoute_iff (T : ℝ) (u : VelocityEvolution) :
    EnvelopeRepFamilyRoute T u ↔
      EnvelopeBudgetFiniteOn T u ∧ EnvelopeBudgetContinuousOn T u := by
  refine ⟨fun ⟨a, ha, hw⟩ => ⟨fun t ht => rep_budget_lt_top (ha t ht),
    hw.congr fun _ ht => envelopeBudget_eq_repFamilyWeight ha ht⟩, ?_⟩
  rintro ⟨hP0, hP1⟩
  obtain ⟨a, ha⟩ := (envelopeBudgetFiniteOn_iff_existsRepFamily T u).mp hP0
  exact ⟨a, ha, repFamilyWeight_continuousOn_of_budgetContinuousOn T u ha hP1⟩

/-! ## 4. The dominated-continuity engine: constructing the bridge input -/

/-- **`h3F` as the `ofReal` of a real Bochner integral.**  Under measurability and
one integrable real domination of the weighted square, the `ℝ≥0∞`-valued `H³` weight
equals `ENNReal.ofReal` of the real integral of the same integrand — the form the
DCT engine consumes. -/
theorem h3F_eq_ofReal_integral {f : ES → ℂ} (hmeas : AEStronglyMeasurable f volume)
    {b : ES → ℝ} (hint : Integrable b volume)
    (hbdd : ∀ᵐ ξ ∂(volume : Measure ES), (1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2 ≤ b ξ) :
    h3F f = ENNReal.ofReal (∫ ξ, (1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2 ∂volume) := by
  unfold h3F
  have hg : (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖f ξ‖ₑ ^ 2)
      = (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2)) := by
    funext ξ
    conv_rhs =>
      rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) 6),
        ENNReal.ofReal_pow (norm_nonneg (f ξ)) 2, ofReal_norm]
  have gnn : 0 ≤ᵐ[volume] (fun ξ => (1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2) :=
    ae_of_all volume fun ξ => mul_nonneg (pow_nonneg (by positivity) 6) (sq_nonneg _)
  have gms : AEStronglyMeasurable (fun ξ => (1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_const.add continuous_norm).pow 6).aestronglyMeasurable
    · exact (hmeas.norm).pow 2
  have hfin : ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * ‖f ξ‖ ^ 2) ∂volume < ⊤ := by
    refine lt_of_le_of_lt
      (lintegral_mono_ae (g := fun ξ => ENNReal.ofReal (b ξ)) ?_) ?_
    · filter_upwards [hbdd] with ξ hξ
      exact ENNReal.ofReal_le_ofReal hξ
    · refine lt_of_le_of_lt
        (lintegral_mono_ae (g := fun ξ => ‖b ξ‖ₑ) ?_) ?_
      · filter_upwards [ae_of_all volume fun ξ => ENNReal.ofReal_le_ofReal (le_abs_self (b ξ))]
          with ξ hξ
        rw [← ofReal_norm]
        exact hξ
      · exact hint.hasFiniteIntegral
  rw [hg, integral_eq_lintegral_of_nonneg_ae gnn gms,
    ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hfin)]

/-- **The dominated-continuity engine.**  Let `a : ℝ → ES → ComplexSpace` be a
family with (i) every slice `t ∈ Ico 0 T` measurable in frequency, (ii) `t ↦ a t ξ`
continuous on `Ico 0 T` for a.e. frequency `ξ`, and (iii) the weighted square
`(1+‖ξ‖)⁶·‖a t ξ i‖²` dominated by ONE integrable envelope for a.e. `ξ`, uniformly
in `t ∈ Ico 0 T` and in the component `i`.  Then the bridge weight map
`t ↦ ⨆ i, h3F (a t · i)` is continuous on `Ico 0 T` — proved by real Bochner DCT on
the `nhdsWithin` filter (`tendsto_integral_filter_of_dominated_convergence`),
rewriting `h3F` through `h3F_eq_ofReal_integral`, and lifting with
`continuous_ofReal`; the `Fin 3` supremum is the binary-max chain
(`iSup_fin_three`, `ContinuousOn.sup`).  This is the row that turns "a constructed
family" into the F-026 §5 bridge hypothesis without assuming P1. -/
theorem continuousOn_h3FWeightMap_of_dominatedContinuousFamily
    {a : ℝ → ES → ComplexSpace} {T : ℝ} {b : ES → ℝ}
    (hmeas : ∀ t ∈ Ico (0 : ℝ) T, ∀ i : Fin 3,
      AEStronglyMeasurable (fun ξ => a t ξ i) volume)
    (hcont : ∀ᵐ ξ ∂(volume : Measure ES), ContinuousOn (fun t => a t ξ) (Ico (0 : ℝ) T))
    (hbdd : ∀ᵐ ξ ∂(volume : Measure ES),
      ∀ t ∈ Ico (0 : ℝ) T, ∀ i : Fin 3,
        (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ≤ b ξ)
    (hint : Integrable b volume) :
    ContinuousOn (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i)) (Ico (0 : ℝ) T) := by
  have weightAESM {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) :
      AEStronglyMeasurable (fun ξ => (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_const.add continuous_norm).pow 6).aestronglyMeasurable
    · exact ((hmeas t ht i).norm).pow 2
  have hset {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) T) :
      Ico (0 : ℝ) T ∈ 𝓝[Ico (0 : ℝ) T] t₀ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨univ, univ_mem, fun _ h => h.2⟩
  have hwt_eq (t₀ : ℝ) (ht₀ : t₀ ∈ Ico (0 : ℝ) T) (i : Fin 3) :
      (fun t => h3F (fun ξ => a t ξ i)) =ᶠ[𝓝[Ico (0 : ℝ) T] t₀]
        (fun t => ENNReal.ofReal (∫ ξ, (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ∂volume)) := by
    refine eventually_of_mem (hset ht₀) ?_
    intro t ht
    have hbdd_ti : ∀ᵐ ξ ∂(volume : Measure ES),
        (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ≤ b ξ := by
      filter_upwards [hbdd] with ξ h
      exact h t ht i
    exact h3F_eq_ofReal_integral (hmeas t ht i) hint hbdd_ti
  have hdct (t₀ : ℝ) (ht₀ : t₀ ∈ Ico (0 : ℝ) T) (i : Fin 3) :
      Tendsto (fun t => ∫ ξ, (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ∂volume)
        (𝓝[Ico (0 : ℝ) T] t₀)
        (𝓝 (∫ ξ, (1 + ‖ξ‖) ^ 6 * ‖a t₀ ξ i‖ ^ 2 ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[Ico (0 : ℝ) T] t₀) b ?_
      ?_ hint ?_
    · refine eventually_of_mem (hset ht₀) ?_
      exact fun t ht => weightAESM ht i
    · refine eventually_of_mem (hset ht₀) ?_
      intro t ht
      filter_upwards [hbdd] with ξ hξ
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (by positivity) 6) (sq_nonneg _))]
      exact hξ t ht i
    · filter_upwards [hcont] with ξ hc
      have h2 : Tendsto (fun t => a t ξ i) (𝓝[Ico (0 : ℝ) T] t₀) (𝓝 (a t₀ ξ i)) :=
        ((continuous_apply i).tendsto (a t₀ ξ)).comp
          ((hc.continuousWithinAt ht₀).tendsto)
      exact ((continuous_const.mul (continuous_norm.pow 2)).tendsto (a t₀ ξ i)).comp h2
  have key (i : Fin 3) :
      ContinuousOn (fun t => h3F (fun ξ => a t ξ i)) (Ico (0 : ℝ) T) := by
    intro t₀ ht₀
    show Tendsto (fun t => h3F (fun ξ => a t ξ i)) (𝓝[Ico (0 : ℝ) T] t₀)
      (𝓝 (h3F (fun ξ => a t₀ ξ i)))
    have hbdd_t0 : ∀ᵐ ξ ∂(volume : Measure ES),
        (1 + ‖ξ‖) ^ 6 * ‖a t₀ ξ i‖ ^ 2 ≤ b ξ := by
      filter_upwards [hbdd] with ξ h
      exact h t₀ ht₀ i
    rw [h3F_eq_ofReal_integral (hmeas t₀ ht₀ i) hint hbdd_t0]
    refine Tendsto.congr' (hwt_eq t₀ ht₀ i).symm ?_
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hdct t₀ ht₀ i)
  have hsup : (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i))
      = (fun t => h3F (fun ξ => a t ξ 0) ⊔ h3F (fun ξ => a t ξ 1) ⊔ h3F (fun ξ => a t ξ 2)) := by
    funext t
    rw [iSup_fin_three]
  rw [hsup]
  exact ((key 0).sup (key 1)).sup (key 2)

/-- **The packaged bridge consumption.**  A dominated continuous `Rep`-family gives
rung P1, through the F-026 §5 bridge. -/
theorem envelopeBudgetContinuousOn_of_dominatedRepFamily {T : ℝ} (u : VelocityEvolution)
    {a : ℝ → ES → ComplexSpace} {b : ES → ℝ}
    (hrep : ∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t))
    (hcont : ∀ᵐ ξ ∂(volume : Measure ES), ContinuousOn (fun t => a t ξ) (Ico (0 : ℝ) T))
    (hbdd : ∀ᵐ ξ ∂(volume : Measure ES),
      ∀ t ∈ Ico (0 : ℝ) T, ∀ i : Fin 3,
        (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ≤ b ξ)
    (hint : Integrable b volume) :
    EnvelopeBudgetContinuousOn T u :=
  envelopeBudget_continuousOn_of_repFamily T u a hrep
    (continuousOn_h3FWeightMap_of_dominatedContinuousFamily
      (fun t ht i => ((measurable_pi_apply i).comp (hrep t ht).datum.meas).aestronglyMeasurable)
      hcont hbdd hint)

/-! ## 5. The named residual: the dominated `Rep`-family route -/

/-- **Rung P1′, the honest carrier of F-026 residual item 4.**  A `Rep`-family
along the evolution that is a.e.-pointwise continuous in time and polynomially
dominated by one integrable frequency envelope.  Item 4 as LITERALLY stated is
equivalent to P0 ∧ P1 (§3) and therefore not a rung; THIS is its non-tautological
reading: a constructive hypothesis whose conjuncts can be verified on an explicit
candidate without first knowing P1.

OBLIGATION: construct such a family from `SolvesBefore` + `RegularOnCompacts`.
The route is the interior-smoothing side of the item-6 audit (OPEN_FRONTIER_MAP,
damped-`Hˢ` row, costs (a)–(c)): the smoothed slice profile at a.e. frequency is
continuous in `t` (the evolution is regular on compacts and the Fourier inversion
integral is dominated on compact time intervals), and the polynomial-weight
domination is the uniform moment bound the same smoothing produces — exactly the
shape the §4 engine consumes.  F-027 caution: the physical-side analogue (Schwartz
decay of slices) is generically FALSE; only the frequency-side, `Rep`-compatible
formulation survives it.  Falsification note: nothing currently exhibited refutes
P1′ on R-solutions; §4 gives its unconditional consumption. -/
def EnvelopeDominatedRepFamilyRoute (T : ℝ) (u : VelocityEvolution) : Prop :=
  ∃ (a : ℝ → ES → ComplexSpace) (b : ES → ℝ),
    (∀ t ∈ Ico (0 : ℝ) T, Rep (u t) (a t)) ∧
    (∀ᵐ ξ ∂(volume : Measure ES), ContinuousOn (fun t => a t ξ) (Ico (0 : ℝ) T)) ∧
    (∀ᵐ ξ ∂(volume : Measure ES), ∀ t ∈ Ico (0 : ℝ) T, ∀ i : Fin 3,
      (1 + ‖ξ‖) ^ 6 * ‖a t ξ i‖ ^ 2 ≤ b ξ) ∧
    Integrable b volume

/-- The dominated route supplies P1 — the §4 engine, packaged at the named prop. -/
theorem envelopeBudgetContinuousOn_of_dominatedRoute {T : ℝ} (u : VelocityEvolution)
    (route : EnvelopeDominatedRepFamilyRoute T u) : EnvelopeBudgetContinuousOn T u := by
  obtain ⟨a, b, hrep, hcont, hbdd, hint⟩ := route
  exact envelopeBudgetContinuousOn_of_dominatedRepFamily u hrep hcont hbdd hint

/-- The dominated route supplies P0 as well (it contains a pointwise `Rep`-family):
a candidate family satisfying P1′ discharges BOTH rungs the bare item-4 form is
equivalent to. -/
theorem envelopeBudgetFiniteOn_of_dominatedRoute {T : ℝ} (u : VelocityEvolution)
    (route : EnvelopeDominatedRepFamilyRoute T u) : EnvelopeBudgetFiniteOn T u := by
  obtain ⟨a, _, hrep, _, _, _⟩ := route
  exact fun t ht => rep_budget_lt_top (hrep t ht)

end Navier.Analysis.EnvelopeRepFamily

set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeRepFamily.EnvelopeRepFamilyRoute
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeRepFamily.EnvelopeDominatedRepFamilyRoute
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeRepFamily.h3EnvelopeBudget_lt_top_iff_existsRep
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeRepFamily.envelopeRepFamilyRoute_iff
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeRepFamily.continuousOn_h3FWeightMap_of_dominatedContinuousFamily
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.h3EnvelopeBudget_lt_top_iff_existsRep
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.rep_h3F_component_lt_top
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.repFamilyWeight_eqOn
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.envelopeRepFamilyRoute_iff
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.continuousOn_h3FWeightMap_of_dominatedContinuousFamily
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeRepFamily.envelopeBudgetContinuousOn_of_dominatedRoute
