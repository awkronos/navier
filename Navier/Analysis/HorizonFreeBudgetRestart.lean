import Navier.Analysis.WienerRestartLeaf
import Navier.Analysis.ClassRestartDecomposition
import Navier.Analysis.RestartEnergyControl
import Navier.Analysis.WienerLocalClassical
import Navier.Analysis.GalerkinRawFamily
import Navier.Problem

/-!
# An explicit envelope control, its BKM budget, and a horizon-free restart

**What this module lands.**  The whole-space row names three producer
obligations before its continuation consumer applies (`restart_paste` is a
consumer of them, not a source): an explicit control `N`, a BKM-style budget
for `N` along `SolvesBefore` members, and a horizon-independent restart
`h = h(ν, M)` whose order is *pre-datum* (F-025: `∀ ν ∀ M ∃ h ∀ u₀ …`, not the
repo leaf's post-datum `∀ ν ∀ u₀ ∀ M ∃ h`).

1. **The control.**  `h3EnvelopeControl T u` is the `Ico 0 T` supremum of
   `h3EnvelopeBudget (u t)`, the Wiener/Lei-Lin `H³` frequency weight
   (`h3F`, weight `(1 + ‖ξ‖) ^ 6`) uniformly over *all* `Rep` representers of
   the slice (`⊤` when the slice has none).  Its exact finite-value
   characterization is `h3EnvelopeBudget_le_iff`, and strict finiteness forces
   representability (`exists_rep_of_lt_top`).
2. **The BKM budget.**  `wienerH3Apriori_h3EnvelopeControl`: *unconditionally*
   (no new hypothesis) the control satisfies `WienerH3Apriori` with budget
   `K = M.toReal`.  The ⊤-guard is what makes the pre-datum order available:
   every representer of every slice is bounded by the same `M`, with no
   reference to the datum.
3. **The restart.**  `horizonIndependentRestartR_h3EnvelopeControl` proves the
   strengthened class form `HorizonIndependentRestartR` (pre-datum, with the
   `RegularOnCompacts` hypothesis/conclusion of the R-engine) for the envelope
   control, and `datumRestartR_of_horizonIndependentRestartR` weakens it to
   the repo's `DatumHorizonIndependentRestartR`.  `crown_from_envelopeApriori`
   reduces the crown to the single premise `APrioriIn RegularOnCompacts
   h3EnvelopeControl`.  Separately, `restart_of_budget` is the plain
   `HorizonIndependentRestart` reduction (the mission's named theorem): from
   budget local existence + *pre-datum* budget propagation + class restart
   uniqueness.  With the energy control's propagation
   (`budgetPropagationDatumFree_preterminalEnergy`) it yields
   `wholeSpaceGlobalRegularity_of_energyBudgetRestart`, whose two remaining
   named inputs are `BudgetLocalExistenceIn trivialClass sliceEnergyBudget`
   and `RestartUniquenessIn trivialClass` (F-023: this is weak-strong
   uniqueness for the full class, genuine dynamical content, not a wrapper).

**Nondegeneracy.**  The energy control carries two exhibits: a concrete
slice-wise nonzero datum with `0 < preterminalEnergyControl T u`
(`exists_preterminalEnergyControl_pos`, the countable bump family's first
element) and a field with `preterminalEnergyControl T u < ⊤`
(`exists_preterminalEnergyControl_lt_top`).  For the envelope control the
`< ⊤` exhibit reduces to a *named* open boundary, recorded here rather than
papered over: `h3EnvelopeBudget v ≤ x` ranges over *all* `Rep v`
representers, so exhibiting one finite upper bound needs the a.e.-uniqueness
of the Wiener profile recovered by the repo's pointwise `fourierInv` route
(`physOf`-injectivity on representers) — no such lemma exists in the repo or
in a directly applicable Mathlib form (the `𝓕`/`𝓕'` duality routes require
Schwartz–Schwartz integrals, not the carrier's `L¹` profile integral).  The
precedent for documenting a control's exhibited-finiteness as a named
residual is `bkmVorticityControl_nondegenerate`.  Nothing in this module
claims global regularity unconditionally: the crown theorems here are
conditional compositions, and the conditional endpoint itself remains open
in the sense of `docs/reviews/W20_NS1_NOTES.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate Topology
open Classical

namespace Navier.Analysis.HorizonFreeBudgetRestart

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.StripOfPiece
open Navier.Analysis.RegularRestart
open Navier.Analysis.RestartPaste
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.ClassRestartDecomposition
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.RestartEnergyControl
open Navier.Analysis.GalerkinBasis

/-! ## 1. The explicit control -/

/-- The Wiener `H³` envelope budget of one velocity slice: the uniform bound
on the `h3F` frequency weight over *all* `Rep` representers of the slice, and
`⊤` when the slice carries no representer at all.  By
`h3EnvelopeBudget_le_iff` this is exactly the greatest lower bound of the
admissible envelope constants `K`; it is not a chosen profile's weight, so it
references no datum. -/
def h3EnvelopeBudget (v : VelocityField) : ℝ≥0∞ :=
  if (∃ a : ES → ComplexSpace, Rep v a) then
    ⨆ (a : ES → ComplexSpace) (_ : Rep v a), ⨆ i : Fin 3, h3F (fun ξ => a ξ i)
  else ⊤

/-- The horizon-`T` envelope control: the supremum of the slice budget over
all constrained times. -/
def h3EnvelopeControl : CriticalQuantity :=
  fun T u => ⨆ t ∈ Ico (0 : ℝ) T, h3EnvelopeBudget (u t)

theorem h3EnvelopeBudget_eq_if (v : VelocityField) :
    h3EnvelopeBudget v =
      if (∃ a : ES → ComplexSpace, Rep v a) then
        ⨆ (a : ES → ComplexSpace) (_ : Rep v a), ⨆ i : Fin 3, h3F (fun ξ => a ξ i)
      else ⊤ := rfl

/-- Every component weight of every representer is bounded by the budget. -/
theorem h3F_component_le_budget {v : VelocityField} {a : ES → ComplexSpace}
    (ha : Rep v a) (i : Fin 3) :
    h3F (fun ξ => a ξ i) ≤ h3EnvelopeBudget v := by
  by_cases hex : ∃ a' : ES → ComplexSpace, Rep v a'
  · rw [h3EnvelopeBudget_eq_if, if_pos hex]
    calc h3F (fun ξ => a ξ i) ≤ ⨆ j : Fin 3, h3F (fun ξ => a ξ j) :=
        le_iSup (fun j => h3F (fun ξ => a ξ j)) i
      _ ≤ ⨆ (a' : ES → ComplexSpace) (_ : Rep v a'), ⨆ j : Fin 3,
            h3F (fun ξ => a' ξ j) := le_iSup₂_of_le a ha le_rfl
  · rw [h3EnvelopeBudget_eq_if, if_neg hex]
    exact le_top

/-- **Exact finite-value characterization.**  For a representable slice, the
budget is bounded by `x` if and only if `x` is an envelope constant that
bounds every representer's every component weight. -/
theorem h3EnvelopeBudget_le_iff {v : VelocityField} (hex : ∃ a, Rep v a) {x : ℝ≥0∞} :
    h3EnvelopeBudget v ≤ x ↔
      (∀ a : ES → ComplexSpace, Rep v a → ∀ i : Fin 3, h3F (fun ξ => a ξ i) ≤ x) := by
  constructor
  · intro h a ha i
    exact (h3F_component_le_budget ha i).trans h
  · intro h
    rw [h3EnvelopeBudget_eq_if, if_pos hex]
    exact iSup₂_le fun a ha => iSup_le fun i => h a ha i

/-- Strict finiteness of the budget forces the slice to be representable
(the ⊤-guard never misfires as a finite value). -/
theorem exists_rep_of_budget_lt_top {v : VelocityField}
    (h : h3EnvelopeBudget v < ⊤) : ∃ a : ES → ComplexSpace, Rep v a := by
  by_contra hn
  rw [h3EnvelopeBudget_eq_if, if_neg hn] at h
  exact lt_irrefl ⊤ h

/-! ## 2. The BKM budget on each `SolvesBefore` member -/

/-- **Item (2), unconditional.**  The envelope control satisfies
`WienerH3Apriori` with `K = M.toReal`.  This is the repo's named BKM-style
premise, *discharged* for the explicit control rather than assumed: along any
`SolvesBefore` solution with `RegularOnCompacts` whose horizon-`T` control is
below `M`, every representer of every preterminal slice has every component
`H³` weight below `M`.  The proof needs no datum: the ⊤-guard makes the
bound uniform in `u₀`. -/
theorem wienerH3Apriori_h3EnvelopeControl : WienerH3Apriori h3EnvelopeControl := by
  intro ν hν u₀ hdiv M
  refine ⟨M.toReal, ?_, ?_⟩
  · positivity
  · intro T hT u p hinit hsol hRu hN τ h1 h2 a ha i
    calc h3F (fun ξ => a ξ i) ≤ h3EnvelopeBudget (u τ) := h3F_component_le_budget ha i
      _ ≤ ⨆ t ∈ Ico (0 : ℝ) T, h3EnvelopeBudget (u t) := le_iSup₂_of_le τ ⟨h1, h2⟩ le_rfl
      _ ≤ (M : ℝ≥0∞) := hN
      _ = ENNReal.ofReal M.toReal := (ENNReal.ofReal_coe_nnreal (p := M)).symm

/-! ## 3. The strengthened R-restart, pre-datum -/

/-- **The pre-datum R-restart order (F-025's strengthening).**  Identical to
the repo's `DatumHorizonIndependentRestartR` except that `∀ M` precedes
`∀ u₀`: the restart length `h = h(ν, M)` is fixed before the datum is
supplied, not after.  This is the class form of the mission's
`HorizonIndependentRestart N`. -/
def HorizonIndependentRestartR (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∃ h : ℝ, 0 < h ∧
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p →
        RegularOnCompacts T u p → PressureNormalizedBefore T p →
        N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          RegularOnCompactsFrom T₀ (T - T₀ + h) w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)

/-- Weakening: the pre-datum form implies the repo's post-datum leaf. -/
theorem datumRestartR_of_horizonIndependentRestartR (N : CriticalQuantity)
    (h : HorizonIndependentRestartR N) : DatumHorizonIndependentRestartR N := by
  intro ν hν u₀ hdiv M
  obtain ⟨hstep, hh, hb⟩ := h ν hν M
  exact ⟨hstep, hh, fun T hT u p hu0 hu hRu hpn hN => hb u₀ hdiv T hT u p hu0 hu hRu hpn hN⟩

/-- **Item (3) for the explicit control.**  The envelope control admits a
pre-datum horizon-independent R-restart with `h = 4π²ν / (3·10⁶·(CW·M + 1))`
depending only on `ν` and `M`.  The Wiener assembly (`piece_at`, `rep_all`,
`strip_of_piece`) runs verbatim under `K := M.toReal` because
`wienerH3Apriori_h3EnvelopeControl`-style bounding is datum-free: the budget
lemma above *is* the smallness input. -/
theorem horizonIndependentRestartR_h3EnvelopeControl :
    HorizonIndependentRestartR h3EnvelopeControl := by
  intro ν hν M
  set K : ℝ := M.toReal with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set C : ℝ := CW.toReal * K with hC
  have hC0 : 0 ≤ C := mul_nonneg ENNReal.toReal_nonneg hK0
  set h : ℝ := 4 * Real.pi ^ 2 * ν / (3 * 10 ^ 6 * (C + 1)) with hhdef
  have hh : 0 < h := by positivity
  have hkey : 10 ^ 6 * (3 * h) * (C + 1) = 4 * Real.pi ^ 2 * ν := by
    rw [hhdef]; field_simp
  have hsmall2 : ∀ L, 0 ≤ L → L ≤ 2 * h → 10 ^ 6 * L * C ≤ 4 * Real.pi ^ 2 * ν := by
    intro L hL0 hL
    rw [← hkey]
    have : L * C ≤ (3 * h) * (C + 1) := by nlinarith
    nlinarith
  refine ⟨h, hh, fun u₀ hdiv T hT u p hu0 hu hRu hpn hN => ?_⟩
  have hKall : ∀ τ : ℝ, 0 ≤ τ → τ < T → ∀ a : ES → ComplexSpace, Rep (u τ) a →
      ∀ i : Fin 3, h3F (fun ξ => a ξ i) ≤ ENNReal.ofReal K := by
    intro τ h1 h2 a ha i
    calc h3F (fun ξ => a ξ i) ≤ h3EnvelopeBudget (u τ) := h3F_component_le_budget ha i
      _ ≤ ⨆ t ∈ Ico (0 : ℝ) T, h3EnvelopeBudget (u t) := le_iSup₂_of_le τ ⟨h1, h2⟩ le_rfl
      _ ≤ (M : ℝ≥0∞) := hN
      _ = ENNReal.ofReal K := (ENNReal.ofReal_coe_nnreal (p := M)).symm
  have h0 : Rep (u 0) (fourierDatum ((-(2 * Real.pi)) • u₀)) := by
    have e : u 0 = fun x => u₀ x := funext hu0
    rw [e]; exact rep_base u₀ hdiv
  have hrep := rep_all hν hK0 hh (hsmall2 _ (by positivity) le_rfl) hu hRu h0 hKall
  set T₀ : ℝ := max (T - h) 0 with hT₀
  have hT₀0 : 0 ≤ T₀ := le_max_right _ _
  have hT₀T : T₀ < T := max_lt (by linarith) hT
  have hT₀h : T - h ≤ T₀ := le_max_left _ _
  set L : ℝ := T - T₀ + h with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hL2 : L ≤ 2 * h := by rw [hLdef]; linarith
  obtain ⟨a, ha⟩ := hrep T₀ hT₀0 hT₀T
  obtain ⟨w, hsol, hR, hw0, -⟩ := piece_at hν hK0 hL0 ha (hKall T₀ hT₀0 hT₀T a ha)
    (hsmall2 L hL0.le hL2)
  obtain ⟨hSF, hRF, hqn, -⟩ := strip_of_piece hν hT₀0 hT₀T (by rw [hLdef]; linarith) hu hRu hpn
    (hsol.normalizePressure) (regularOnCompacts_normalize _ _ _ hR)
    (normalizePressure_normalizedBefore _ _) hw0
  refine ⟨T₀, hT₀0, hT₀T, _, _, fun t _ ht => (if_pos ht).symm, fun t _ ht => (if_pos ht).symm,
    hSF, hRF, fun t h1 h2 => hqn t h1 (by rw [hLdef]; linarith)⟩

/-- **The crown reduction for the explicit control.**  The whole-space
endpoint for `h3EnvelopeControl` is reduced to the single remaining producer
input — the damped-`H³` a priori estimate `APrioriIn RegularOnCompacts
h3EnvelopeControl` — through the pre-datum restart above. -/
theorem crown_from_envelopeApriori
    (hapriori : APrioriIn RegularOnCompacts h3EnvelopeControl) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_R_restart_apriori h3EnvelopeControl
    (datumRestartR_of_horizonIndependentRestartR h3EnvelopeControl
      horizonIndependentRestartR_h3EnvelopeControl) hapriori

/-! ## 4. The plain-engine reduction `restart_of_budget` -/

/-- Slice budget of the trivial class: the kinetic energy of the slice, in the
extended reals through the constant-in-time evolution. -/
def sliceEnergyBudget (v : VelocityField) : ℝ≥0∞ :=
  ENNReal.ofReal (kineticEnergy (fun _ => v) (0 : ℝ))

/-- **Pre-datum budget propagation.**  The repo's `BudgetPropagationIn` with
the datum moved *after* the budget bound `M` (`∀ ν ∀ M ∃ K ∀ u₀ …`), so that
the restart chain feeding the plain `HorizonIndependentRestart` engine never
needs `K` to depend on `u₀`. -/
def BudgetPropagationDatumFree (C : SolutionClass) (B : VelocityField → ℝ≥0∞)
    (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∃ K : ℝ≥0,
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ → ∀ T : ℝ, 0 < T →
      ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        N T u ≤ (M : ℝ≥0∞) → ∀ t : ℝ, 0 ≤ t → t < T → B (u t) ≤ (K : ℝ≥0∞)

/-- **The energy instance of pre-datum propagation**: `K = M`, from the
`SolvesBefore` energy inequality packaged in the preterminal supremum. -/
theorem budgetPropagationDatumFree_preterminalEnergy :
    BudgetPropagationDatumFree trivialClass sliceEnergyBudget preterminalEnergyControl := by
  intro ν hν M
  refine ⟨M, fun u₀ hu₀ T hT u p hinit hsol hmem hN t h1 h2 => ?_⟩
  show ENNReal.ofReal (kineticEnergy (fun _ => u t) 0) ≤ (M : ℝ≥0∞)
  calc ENNReal.ofReal (kineticEnergy (fun _ => u t) 0)
      = ENNReal.ofReal (kineticEnergy u t) := rfl
    _ ≤ ⨆ s ∈ Ico (0 : ℝ) T, ENNReal.ofReal (kineticEnergy u s) :=
        le_iSup₂_of_le t ⟨h1, h2⟩ le_rfl
    _ ≤ (M : ℝ≥0∞) := hN

/-- Pressure agreement at the restart time itself.  On the open window the
interior lemma identifies the pressures; at `T₀` both slice maps are the
evaluation of jointly smooth fields at points of their strips, so the two
limits along `𝓝[>] T₀` coincide with their values and the common limit is
unique. -/
private theorem pressure_eq_at_left {ν T T₀ L : ℝ} {u w : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T) (hTL : T ≤ T₀ + L)
    (hsol : SolvesBefore ν T u p) (hw : SolvesFrom ν T₀ L w q)
    (hpn : PressureNormalizedBefore T p)
    (hqn : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → q t 0 = 0)
    (hagree : ∀ t : ℝ, T₀ ≤ t → t < T → t < T₀ + L → u t = w t)
    (x : Space) : p T₀ x = q T₀ x := by
  have hpeq : ∀ t : ℝ, T₀ < t → t < T → p t = q t := by
    intro t ht0 htT
    exact pressure_eq_of_velocity_eq_interior hT₀ hsol hw hpn hqn hagree ht0 htT
      (by linarith)
  obtain ⟨_, hp, _, _⟩ := hsol.classical
  obtain ⟨_, wp, -, -, -, -⟩ := hw
  have hcp : ContinuousWithinAt (fun z : ℝ × Space => p z.1 z.2)
      (spacetimeBefore T) (T₀, x) :=
    (ContDiffOn.continuousOn hp).continuousWithinAt ⟨⟨hT₀, hT₀T⟩, trivial⟩
  have hcq : ContinuousWithinAt (fun z : ℝ × Space => q z.1 z.2)
      (Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space)) (T₀, x) :=
    (ContDiffOn.continuousOn wp).continuousWithinAt ⟨⟨le_rfl, by linarith⟩, trivial⟩
  have hmap : Tendsto (fun t : ℝ => ((t, x) : ℝ × Space)) (nhdsWithin T₀ (Ioi T₀))
      (𝓝 (T₀, x)) := by
    have h0 := (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (x : Space)) (nhdsWithin T₀ (Ioi T₀)) (𝓝 x))
    rw [← nhds_prod_eq (x := (T₀ : ℝ)) (y := x)] at h0
    exact h0
  have hit : Iio (T : ℝ) ∈ 𝓝 T₀ := isOpen_Iio.mem_nhds hT₀T
  have hlimp : Tendsto (fun t : ℝ => ((t, x) : ℝ × Space)) (nhdsWithin T₀ (Ioi T₀))
      (𝓝[(spacetimeBefore T)] (T₀, x)) :=
    tendsto_inf.2 ⟨hmap, tendsto_principal.2 <| by
      filter_upwards [(tendsto_id.mono_left nhdsWithin_le_nhds).eventually hit,
        self_mem_nhdsWithin] with t hlt ht
      exact Set.mem_prod.2 ⟨Set.mem_Ico.2 ⟨le_trans hT₀ ht.le, hlt⟩,
        Set.mem_univ _⟩⟩
  have hlimq : Tendsto (fun t : ℝ => ((t, x) : ℝ × Space)) (nhdsWithin T₀ (Ioi T₀))
      (𝓝[(Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space))] (T₀, x)) :=
    tendsto_inf.2 ⟨hmap, tendsto_principal.2 <| by
      have hIL : Iio (T₀ + L : ℝ) ∈ 𝓝 T₀ :=
        isOpen_Iio.mem_nhds (show T₀ < T₀ + L by linarith)
      filter_upwards [(tendsto_id.mono_left nhdsWithin_le_nhds).eventually hIL,
        self_mem_nhdsWithin] with t hlt ht
      exact Set.mem_prod.2 ⟨Set.mem_Ico.2 ⟨ht.le, hlt⟩, Set.mem_univ _⟩⟩
  exact tendsto_nhds_unique (hcp.tendsto.comp hlimp)
    ((hcq.tendsto.comp hlimq).congr' <| by
      filter_upwards [self_mem_nhdsWithin,
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually hit] with t ht hlt
      exact (congrFun (hpeq t ht hlt) x).symm)

/-- **The mission's named reduction.**  Budget local existence, *pre-datum*
budget propagation, and class restart uniqueness (instantiated at the trivial
class, so the class premises are `True`) compose to the plain
`HorizonIndependentRestart N` of `Navier.Analysis.RestartPaste`: step `h / 2`,
restart time `T₀ = max 0 (T − h / 2)`, velocity agreement by uniqueness, and
pressure agreement on the whole closed window `[T₀, T)` — the interior by
`pressure_eq_of_velocity_eq_interior`, at `T₀` by the continuity squeeze
`pressure_eq_at_left`. -/
theorem restart_of_budget {B : VelocityField → ℝ≥0∞} {N : CriticalQuantity}
    (hloc : BudgetLocalExistenceIn trivialClass B)
    (hprop : BudgetPropagationDatumFree trivialClass B N)
    (huniq : RestartUniquenessIn trivialClass) : HorizonIndependentRestart N := by
  intro ν hν M
  obtain ⟨K, hK⟩ := hprop ν hν M
  obtain ⟨h, hh, hrestart⟩ := hloc ν hν K
  refine ⟨h / 2, by positivity, fun u₀ hu₀ T hT u p hinit hsol hnorm hN => ?_⟩
  set T₀ : ℝ := max 0 (T - h / 2) with hT₀_def
  have hT₀0 : 0 ≤ T₀ := le_max_left _ _
  have hT₀T : T₀ < T := max_lt hT (by linarith)
  have hTle : T - T₀ ≤ h / 2 := by
    have := le_max_right 0 (T - h / 2)
    linarith
  have hB : B (u T₀) ≤ (K : ℝ≥0∞) := hK u₀ hu₀ T hT u p hinit hsol trivial hN T₀ hT₀0 hT₀T
  obtain ⟨w, q, hw0, hw, hqn, hwmem⟩ := hrestart T₀ T hT₀0 hT₀T u p hsol trivial hB
  have hagree_v : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t := fun t ht htT =>
    huniq ν hν T₀ T h hT₀0 hT₀T hh u p w q hsol trivial hw trivial hw0 t ht htT (by linarith)
  refine ⟨T₀, hT₀0, hT₀T, w, q, hagree_v, ?_, solvesFrom_mono_right hw (by linarith),
    fun t ht htL => hqn t ht (by linarith)⟩
  intro t ht0 htT
  by_cases ht0eq : t = T₀
  · subst ht0eq
    funext x
    exact pressure_eq_at_left hT₀0 hT₀T (by linarith) hsol hw hnorm hqn
      (fun s hs hsT _ => hagree_v s hs hsT) x
  · refine pressure_eq_of_velocity_eq_interior hT₀0 hsol hw hnorm hqn
      (fun s hs hsT _ => hagree_v s hs hsT) ?_ htT (by linarith)
    exact lt_of_le_of_ne ht0 (Ne.symm ht0eq)

/-! ## 5. Nondegeneracy exhibits for the energy control, and the endpoint -/

/-- The preterminal energy control is genuinely positive on a concrete
admissible slice: the first element of the countable bump family
`shiftSchwartz 0` has strictly positive kinetic energy, so its horizon-`1`
control is nonzero.  (Non-degenerate in the direction F-025 requires: `N` is
not the identically-zero quantity.) -/
theorem exists_preterminalEnergyControl_pos :
    ∃ (T : ℝ) (u : VelocityEvolution), 0 < preterminalEnergyControl T u := by
  obtain ⟨x0, hx0⟩ : ∃ x : Space, shiftSchwartz (0 : Space) x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply shiftSchwartz_ne_zero (0 : Space)
    exact DFunLike.coe_injective (by funext y; exact hcon y)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin 3, shiftSchwartz (0 : Space) x0 i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx0
    ext i
    exact hcon i
  have hcont : Continuous (fun x : Space => ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (shiftSchwartz (0 : Space)).continuous).pow 2)
  have hsupp : HasCompactSupport
      (fun x : Space => ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2) := by
    have hs : HasCompactSupport (shiftPhi (0 : Space)) := shiftPhi_hasCompactSupport _
    have hsub : Function.support
        (fun x : Space => ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2) ⊆
        Function.support (shiftPhi (0 : Space)) := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hcon
      apply hx
      have hz : shiftSchwartz (0 : Space) x = 0 := by
        rw [shiftSchwartz_apply]; exact hcon
      exact Finset.sum_eq_zero (fun i _ => by rw [congrFun hz i, Pi.zero_apply,
        zero_pow two_ne_zero])
    exact hs.mono hsub
  have hnonneg : 0 ≤ fun x : Space => ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2 :=
    fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hfne : (fun x : Space => ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2) x0 ≠ 0 := by
    intro hzsum
    have hz : ∑ i : Fin 3, (shiftSchwartz (0 : Space) x0 i) ^ 2 = 0 := hzsum
    have hle : (shiftSchwartz (0 : Space) x0 i0) ^ 2 ≤
        ∑ i : Fin 3, (shiftSchwartz (0 : Space) x0 i) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i0)
    rw [hz] at hle
    linarith [sq_pos_of_ne_zero hi0]
  have hpos : 0 < ∫ x : Space, ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2 :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcont hsupp hnonneg hfne
  have hkin0 :
      0 < kineticEnergy (fun _ => (⇑(shiftSchwartz (0 : Space)) : VelocityField)) 0 := by
    show 0 < ∫ x : Space, ∑ i : Fin 3, (shiftSchwartz (0 : Space) x i) ^ 2
    exact hpos
  refine ⟨1, fun _ => ⇑(shiftSchwartz (0 : Space)), ?_⟩
  exact (ENNReal.ofReal_pos.mpr hkin0).trans_le
    (ofReal_kineticEnergy_zero_le_preterminalEnergyControl _ zero_lt_one)

/-- The preterminal energy control is genuinely finite on a concrete slice:
the zero evolution has horizon-`1` control `0 < ⊤`.  (Non-degenerate in the
complementary direction: `N` is not the identically-`⊤` quantity.) -/
theorem exists_preterminalEnergyControl_lt_top :
    ∃ (T : ℝ) (u : VelocityEvolution), preterminalEnergyControl T u < ⊤ := by
  refine ⟨1, fun _ _ => (0 : Space), ?_⟩
  have h0 : preterminalEnergyControl 1 (fun _ _ => (0 : Space)) = 0 := by
    refine le_antisymm (iSup₂_le fun t _ => ?_) zero_le
    have hlam : (fun x : Space => ∑ i : Fin 3, ((fun _ _ => (0 : Space)) t x i) ^ 2) = 0 := by
      ext x
      refine Finset.sum_eq_zero (fun i _ => ?_)
      show ((0 : Space) i) ^ 2 = 0
      rw [Pi.zero_apply, zero_pow two_ne_zero]
    have hle : ∫ x : Space, ∑ i : Fin 3, ((fun _ _ => (0 : Space)) t x i) ^ 2 ≤ 0 := by
      rw [hlam, integral_zero']
    exact (ENNReal.ofReal_eq_zero.2
      (show kineticEnergy (fun _ _ => (0 : Space)) t ≤ 0 from hle)).le
  rw [h0]
  exact ENNReal.zero_lt_top

/-- **The energy-route crown from the budget triple.**  The original
whole-space consumer, with its restart premise produced by
`restart_of_budget` through the pre-datum energy propagation: the two
remaining named inputs are `BudgetLocalExistenceIn trivialClass
sliceEnergyBudget` (slice-energy-budgeted local continuation) and
`RestartUniquenessIn trivialClass` (F-023: full-class restart uniqueness,
i.e. weak-strong uniqueness — genuine dynamical content).  Local existence
itself is unconditional on this carrier. -/
theorem wholeSpaceGlobalRegularity_of_energyBudgetRestart
    (hloc : BudgetLocalExistenceIn trivialClass sliceEnergyBudget)
    (huniq : RestartUniquenessIn trivialClass) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_local_horizonIndependentEnergyRestart
    Navier.Analysis.WienerLocalClassical.localClassicalExistence
    (restart_of_budget hloc budgetPropagationDatumFree_preterminalEnergy huniq)

end Navier.Analysis.HorizonFreeBudgetRestart

#check Navier.Analysis.HorizonFreeBudgetRestart.h3EnvelopeBudget
#check Navier.Analysis.HorizonFreeBudgetRestart.h3EnvelopeControl
#check Navier.Analysis.HorizonFreeBudgetRestart.HorizonIndependentRestartR
#check Navier.Analysis.HorizonFreeBudgetRestart.BudgetPropagationDatumFree
#check Navier.Analysis.HorizonFreeBudgetRestart.sliceEnergyBudget
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.h3F_component_le_budget
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.h3EnvelopeBudget_le_iff
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.exists_rep_of_budget_lt_top
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.wienerH3Apriori_h3EnvelopeControl
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.datumRestartR_of_horizonIndependentRestartR
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.horizonIndependentRestartR_h3EnvelopeControl
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.crown_from_envelopeApriori
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.budgetPropagationDatumFree_preterminalEnergy
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.restart_of_budget
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.exists_preterminalEnergyControl_pos
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.exists_preterminalEnergyControl_lt_top
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.wholeSpaceGlobalRegularity_of_energyBudgetRestart
