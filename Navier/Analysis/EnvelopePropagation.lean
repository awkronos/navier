import Navier.Analysis.EnvelopeDatumSeed
import Navier.Analysis.DampedThresholdGronwall
import Navier.Analysis.ClassDecomposition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Propagating the envelope budget in time: the F-026 propagation rung, landed as a board

**Mission.**  The seed `Navier/Analysis/EnvelopeDatumSeed.lean` (72f459a) landed the
base case `envelopeBudget_datumSeed` of the bootstrap of the crown's single remaining
premise `APrioriIn RegularOnCompacts h3EnvelopeControl`
(`crown_from_envelopeApriori`, `Navier.Analysis.HorizonFreeBudgetRestart`).  Its
receipt names the next rung: the *propagation* side — time-continuity of
`t ↦ h3EnvelopeBudget (u t)` along `SolvesBefore` members, and the two hypotheses
`hAc`/`hAd` of `Navier.Analysis.DampedThresholdGronwall.threshold_gronwall_uniform`
which are "supplied nowhere" for the envelope.  This module lands the structural
rungs that follow from the carrier as stated, supplies `hAc`/`hAd` for a concrete
running integral, packages the bootstrap at a horizon into an
`h3EnvelopeControl`-bounded conclusion, and states every genuinely analytic rung
that remains open as its own named `Prop` (the estate's decomposition idiom) so the
next lane inherits a checkered board, not prose.

**What is unconditional here.**  (§1) Structural squeeze rows for the budget map
along an evolution: the initial-slice finiteness *transported to evolutions*
(`envelopeBudget_init_lt_top`, `envelopeBudget_init_eq_datumWeight` — the seed's
datum row rewritten along `u 0 = u₀`), the control characterization
(`h3EnvelopeControl_le_iff` — the bootstrap's sublevel set, exactly), horizon
monotonicity, `budget ≤ control`, and
`exists_rep_of_control_lt_top` (a finite horizon-control makes every slice
representable).  (§2) The hAc/hAd supply: `continuousOn_runningIntegral`
(`intervalIntegral.continuousOn_primitive_interval`) and
`hasDerivWithinAt_runningIntegral` (moving-endpoint FTC `integral_hasDerivAt_right`
after a Tietze extension of the rate to all of `ℝ`, which is what makes the
`HasDerivWithinAt … (Ici t) t` right-derivatives hold at the endpoint `t = 0` as
well as in the interior), packaged in
`threshold_gronwall_uniform_of_continuousRate`: in that row the `hAc`/`hAd` seats of
the repo's threshold Gronwall are *discharged by construction* from
`ContinuousOn a (Icc 0 T)`, so the residue is only the rate itself.  (§3) The five
named analytic rungs P0–P4 as `Prop`s with proof-obligation docstrings — the honest
decomposition of what is left.  (§4) The bootstrap schema's closed side and base:
`envelopeSublevel_isClosed` (sublevel sets
of the budget map are closed once P1 holds, via `IsClosed.isClosed_le`) and
`zero_in_envelopeSublevel`.  (§5) The reduction bridge
`envelopeBudget_continuousOn_of_repFamily`: by the collapse
`h3EnvelopeBudget_eq_iSup`, the envelope's time-continuity is *the same statement*
as continuity of the explicit weight map of ONE continuous representer family —
the named route for P1.  (§6) The packaged propagation rung
`envelopeBootstrap_at_horizon`: P0–P4 for one solution-horizon imply
`h3EnvelopeControl T u ≤ ENNReal.ofReal (exp B − 1)` with
`B = (c + max (log(1 + (budget u 0).toReal)) Λ)·exp M − c`, via
`threshold_gronwall_uniform` on every closed sub-horizon and the
`control_le_iff` squeeze.  (Same section) The crown seat: `EnvelopeBootstrapBoard` (one named
Prop bundling P0–P4 for a datum) and `aprioriIn_of_envelopeBootstrapBoard` — the
board holding uniformly per datum supplies the crown premise `APrioriIn
RegularOnCompacts h3EnvelopeControl` *discharged*, not assumed.

**What remains open (the named residual list — this is the honest F-026 verdict).**
The propagation rung is NOT closed tonight: the carrier `SolvesBefore` +
`RegularOnCompacts` carries no time-continuity of slices in any topology that
`h3EnvelopeBudget` sees (ledger F-026: "a jointly smooth evolution with
finite-energy slices need not be `L²`-continuous in time"), and positive-time Wiener
representability of R-slices (P0) requires the frequency-moment persistence whose
input — interior smoothing from the PDE — is exactly the item-6 audit costs (a),
(b), (c) recorded in the OPEN_FRONTIER_MAP (damped-`Hˢ` row), with F-027 as the
cautionary precedent for the physical-side variant (Schwartz decay is generically
lost at positive times).  The precise named lemmas separating this module from
closing the crown premise:
1. `EnvelopeBudgetFiniteOn` (P0) — persistence of `Rep`-representability of slices
   along `SolvesBefore` + `RegularOnCompacts` members; route: interior `Hˢ`
   smoothing gives all Fourier moments of the slice profile, then `WDatum` and the
   pointwise inversion `u t x = physOf (fourierDatum …) x`.
2. `EnvelopeBudgetContinuousOn` (P1) — time-continuity of the envelope map; route:
   item 4 of this list plus `envelopeBudget_continuousOn_of_repFamily` with a
   family whose weight map is continuous (weighted-`L²` dominated convergence —
   the seed's `h3F_lt_top_of_schwartz` domination is the same shape).
3. `EnvelopeBudgetRightDerivative` (P2) — the right derivative of `envelopeZ u`
   exists on `[0,T)`; the damped-`Hˢ` differential-inequality machinery on the
   envelope carrier.
4. A continuous `Rep`-family of representers — the input to
   `envelopeBudget_continuousOn_of_repFamily`: `∀ t ∈ Ico 0 T, Rep (u t) (a t)`
   with `t ↦ ⨆ i, h3F (a t · i)` continuous.
5. `EnvelopeRateBudget` (P3) — the rate whose running integral is `A`: its
   `ContinuousOn … (Ico 0 T)` clause is exactly the field
   `BKMControl.rate_continuousOn` (`Navier/Analysis/BealeKatoMajda.lean`), so the
   hAc/hAd seats inherit from a `BKMControl` on the sub-horizons; its budget clause
   `∫₀ᵗ rate ≤ M` is the BKM-budget input of the damped estimate.
6. `EnvelopeDampedRateInequality` (P4) — the threshold growth inequality
   `Z' ≤ a·(c + Z)` above `Λ`: the content of
   `DampedThresholdGronwall.damped_rate_reduction` plus `SobolevInterpolation`
   re-carried on the envelope (Wiener-`H³`) carrier, which is the Clay-grade core
   and the same estimate that blocks `APrioriCriticalControlIn`-style rows
   elsewhere in the ledger (F-025, F-028).
No statement here claims global regularity unconditionally: every headline is
either structural, a discharged seat in a packaging row, or a named `Prop`.

**Placement note.**  This module sits downstream of `EnvelopeDatumSeed`,
`EnvelopeFourierUniqueness` and `HorizonFreeBudgetRestart` (it imports the seed,
which imports both others) and of `DampedThresholdGronwall` (whose
`threshold_gronwall_uniform` it packages).  It therefore cannot live in the
`HorizonFreeBudgetRestart` namespace — the same cycle evidence the seed recorded
(HBR-cycle): `EnvelopeFourierUniqueness` line 1 imports HBR, so nothing upstream
can import downstream rows.  The namespace is the module's own, per the repo's
one-namespace-per-file convention (precedent: `EnvelopeDatumSeed` §Placement).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate BigOperators

namespace Navier.Analysis.EnvelopePropagation

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.EnvelopeFourierUniqueness
open Navier.Analysis.EnvelopeDatumSeed
open Navier.Analysis.DampedThresholdGronwall
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition

/-! ## 1. Structural rows: the seed transported to evolutions, and the control squeeze -/

/-- The datum-profile envelope weight `M₀`: the value the seed
`envelopeBudget_datumSeed` identifies the initial-slice budget with. -/
noncomputable def datumWeight (u₀ : SchwartzVelocity) : ℝ≥0∞ :=
  ⨆ i : Fin 3, h3F (fun ξ => fourierDatum ((-(2 * Real.pi)) • u₀) ξ i)

/-- **Base case for evolutions.**  The seed's datum-level finiteness transported
along the initial condition: every `VelocityEvolution` with Schwartz divergence-free
initial datum has finite envelope budget at `t = 0`.  This is the nonempty base of
the bootstrap schema on sublevel sets of the budget map. -/
theorem envelopeBudget_init_lt_top (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (hdiv : DivergenceFreeInitial u₀) (u : VelocityEvolution)
    (hinit : ∀ x : Space, u 0 x = u₀ x) : h3EnvelopeBudget (u 0) < ⊤ := by
  rw [funext hinit]
  exact (envelopeBudget_datumSeed ν hν u₀ hdiv).1

/-- The same, pinned to the bootstrap constant: `h3EnvelopeBudget (u 0)` *equals*
the datum weight `datumWeight u₀`. -/
theorem envelopeBudget_init_eq_datumWeight (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity)
    (hdiv : DivergenceFreeInitial u₀) (u : VelocityEvolution)
    (hinit : ∀ x : Space, u 0 x = u₀ x) : h3EnvelopeBudget (u 0) = datumWeight u₀ := by
  rw [funext hinit]
  exact (envelopeBudget_datumSeed ν hν u₀ hdiv).2

/-- Each slice budget is bounded by the horizon control. -/
theorem h3EnvelopeBudget_le_control (u : VelocityEvolution) {T t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : h3EnvelopeBudget (u t) ≤ h3EnvelopeControl T u :=
  le_iSup₂_of_le t ht le_rfl

/-- **Exact sublevel characterization.**  The horizon control is at most `x` iff
every constrained slice budget is.  This is the bootstrap's working set identity:
the set `{t | h3EnvelopeBudget (u t) ≤ K}` is exactly the preimage under `u` of the
sublevel of the control. -/
theorem h3EnvelopeControl_le_iff (u : VelocityEvolution) {T : ℝ} {x : ℝ≥0∞} :
    h3EnvelopeControl T u ≤ x ↔ ∀ t ∈ Ico (0 : ℝ) T, h3EnvelopeBudget (u t) ≤ x :=
  iSup₂_le_iff

/-- Monotonicity of the horizon control in the horizon. -/
theorem h3EnvelopeControl_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) (u : VelocityEvolution) :
    h3EnvelopeControl T₁ u ≤ h3EnvelopeControl T₂ u :=
  iSup₂_le fun t ht => le_iSup₂_of_le t ⟨ht.1, lt_of_lt_of_le ht.2 h⟩ le_rfl

/-- A horizon with finite envelope control makes *every* preterminal slice
representable (the budget's `⊤`-guard never survives a finite control). -/
theorem exists_rep_of_control_lt_top {T : ℝ} {u : VelocityEvolution}
    (h : h3EnvelopeControl T u < ⊤) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ a : ES → ComplexSpace, Rep (u t) a :=
  exists_rep_of_budget_lt_top ((h3EnvelopeBudget_le_control u ht).trans_lt h)

/-! ## 2. The `hAc`/`hAd` seats of `DampedThresholdGronwall`, discharged for a running integral -/

/-- **`hAc` supplied.**  The running integral of a rate continuous on `[0, T]` is
continuous on `[0, T]`: `intervalIntegral.continuousOn_primitive_interval` under
`ContinuousOn.integrableOn_compact`. -/
theorem continuousOn_runningIntegral {T : ℝ} (hT : 0 ≤ T) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => ∫ x in (0 : ℝ)..t, a x ∂volume) (Icc (0 : ℝ) T) := by
  have h1 := continuousOn_primitive_interval (μ := volume) (by
    rw [Set.uIcc_of_le hT]
    exact ha.integrableOn_compact isCompact_Icc)
  exact h1.mono Set.Icc_subset_uIcc

/-- **`hAd` supplied.**  The running integral has the right derivative `a t` at
every `t ∈ [0, T)`, including the endpoint `t = 0`.  The endpoint is exactly what
the two-sided moving-boundary FTC `intervalIntegral.integral_hasDerivAt_right`
does not give for a rate defined only on `[0, T]`: the fix is a Tietze extension
(`ContinuousMap.exists_restrict_eq`, `isClosed_Icc`, `Real.instTietzeExtension`) of
the rate to a function continuous on all of `ℝ`; the extended and original running
integrals agree near `t` along `Ici t` (both integrate over `[0, u] ⊆ [0, T]`
there), and `HasDerivWithinAt.congr` transports the derivative. -/
theorem hasDerivWithinAt_runningIntegral {T : ℝ} (hT : 0 ≤ T) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, a x ∂volume) (a t) (Ici t) t := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_Icc
    (⟨fun z : ↥(Icc (0 : ℝ) T) => a z, ha.domRestrict⟩ :
      ContinuousMap (↥(Icc (0 : ℝ) T)) ℝ)
  set ã : ℝ → ℝ := (g : ℝ → ℝ) with hãdef
  have hcg : Continuous ã := by rw [hãdef]; exact g.continuous
  have hagree : ∀ u ∈ Icc (0 : ℝ) T, ã u = a u := by
    intro u hu
    exact congrArg (fun Φ : ContinuousMap (↥(Icc (0 : ℝ) T)) ℝ => Φ ⟨u, hu⟩) hg
  -- the two primitives agree near `t` along `Ici t`
  have hlt : ∀ᶠ w in 𝓝[Ici t] t, w < T := by
    have h1 : ∀ᶠ w in 𝓝 t, w ∈ Iio T := isOpen_Iio.eventually_mem ht.2
    show ∀ᶠ w in 𝓝 t ⊓ 𝓟 (Ici t), w < T
    exact eventually_inf_principal.mpr (h1.mono fun w hw _ => hw)
  have hprim : (fun u => ∫ x in (0 : ℝ)..u, a x ∂volume)
      =ᶠ[𝓝[Ici t] t] (fun u => ∫ x in (0 : ℝ)..u, ã x ∂volume) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with u hut huT
    have hu0 : (0 : ℝ) ≤ u := le_trans ht.1 hut.ge
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hu0] at hx
    exact (hagree x ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 huT)⟩).symm
  have hval : (fun u => ∫ x in (0 : ℝ)..u, a x ∂volume) t
      = (fun u => ∫ x in (0 : ℝ)..u, ã x ∂volume) t := by
    show ∫ x in (0 : ℝ)..t, a x ∂volume = ∫ x in (0 : ℝ)..t, ã x ∂volume
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le ht.1] at hx
    exact (hagree x ⟨hx.1, le_trans hx.2 (le_of_lt ht.2)⟩).symm
  have hd : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, ã x ∂volume) (ã t) t :=
    integral_hasDerivAt_right (hcg.intervalIntegrable (0 : ℝ) t)
      (hcg.stronglyMeasurableAtFilter volume (𝓝 t)) hcg.continuousAt
  have hw : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, a x ∂volume) (ã t) (Ici t) t :=
    (hd.hasDerivWithinAt (s := Ici t)).congr_of_eventuallyEq hprim hval
  exact hw.congr_deriv (hagree t ⟨ht.1, le_of_lt ht.2⟩)

/-- **The packaged uniform threshold Gronwall with `hAc`/`hAd` discharged.**  The
two seats of `threshold_gronwall_uniform` are filled by the running integral of any
`a` continuous on `[0, T]`; the residue is the rate's nonnegativity, its budget
bound `∫₀ᵗ a ≤ M`, and the `Z`-side hypotheses.  This is the row that turns the
receipt phrase "`hAc`/`hAd` supplied nowhere" into "supplied by construction, from
`ContinuousOn a`". -/
theorem threshold_gronwall_uniform_of_continuousRate {Z Z' a : ℝ → ℝ} {T Λ c M : ℝ}
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hΛ : 0 ≤ Λ)
    (hZc : ContinuousOn Z (Icc (0 : ℝ) T))
    (hZd : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (ha : ContinuousOn a (Icc (0 : ℝ) T))
    (ha0 : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (hAM : ∀ t ∈ Icc (0 : ℝ) T, ∫ x in (0 : ℝ)..t, a x ∂volume ≤ M)
    (hineq : ∀ t ∈ Ico (0 : ℝ) T, Λ < Z t → Z' t ≤ a t * (c + Z t)) :
    ∀ t ∈ Icc (0 : ℝ) T, Z t ≤ (c + max (Z 0) Λ) * Real.exp M - c :=
  threshold_gronwall_uniform hc hΛ hZc hZd
    (continuousOn_runningIntegral hT ha)
    (fun t ht => hasDerivWithinAt_runningIntegral hT ha ht)
    (by simp) ha0 hAM hineq

/-! ## 3. The named rungs (P0–P4): each a `Prop` with its obligation -/

/-- **Rung P0 — persistence of representability.**  Every constrained slice carries
a `Rep` representer, i.e. the budget's `⊤`-guard never fires along the evolution.

OBLIGATION (F-026/F-027 route): for a `SolvesBefore` + `RegularOnCompacts` member
with Schwartz datum, every slice `t > 0` is represented.  The mathematical input is
the interior-smoothing side of the item-6 audit (OPEN_FRONTIER_MAP, damped-`Hˢ` row,
costs (a)-(c): a smooth slice with all derivatives in `L²` has a Fourier profile in
`L¹` with all polynomial moments — `WDatum` — and the pointwise inversion identifies
it with `physOf`).  Cautionary precedent F-027: the analogous statement for
physical-side Schwartz persistence is FALSE generically (Brandolese's `|x|⁻⁴`
decay); this rung is the frequency-side variant, whose physical decay may be
slow — the `Rep` carrier asks only smoothness-class content, which is exactly why
it survives F-027.  Falsification note: nothing currently exhibited refutes P0 on
R-solutions; it is unproved, not false-at-known-evidence. -/
def EnvelopeBudgetFiniteOn (T : ℝ) (u : VelocityEvolution) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, h3EnvelopeBudget (u t) < ⊤

/-- **Rung P1 — the F-026 continuity rung, envelope form.**  The budget map is
continuous on `[0, T)`.

OBLIGATION (F-026's named gap, specialized): the carrier has no time-continuity
field in any topology the budget sees — a jointly smooth evolution with
finite-energy slices need not be continuous in time for *any* global weighted norm
(ledger: a bump translated to infinity as `t ↓ 0`, extended by zero).  Route:
`envelopeBudget_continuousOn_of_repFamily` (§5 bridge) reduces P1 to supplying one
continuous `Rep`-family along the solution — the family itself is rung 4 of the
residual list.  With P1, the closed side of the bootstrap is unconditional
(`envelopeSublevel_isClosed`). -/
def EnvelopeBudgetContinuousOn (T : ℝ) (u : VelocityEvolution) : Prop :=
  ContinuousOn (fun t => h3EnvelopeBudget (u t)) (Ico (0 : ℝ) T)

/-- The log envelope map `Z`: the `threshold_gronwall` witness, pinned to the
budget under rung P0 (then `exp (envelopeZ u t) - 1 = (h3EnvelopeBudget (u t)).toReal`
and the budget is `ENNReal.ofReal` of it). -/
noncomputable def envelopeZ (u : VelocityEvolution) (t : ℝ) : ℝ :=
  Real.log (1 + (h3EnvelopeBudget (u t)).toReal)

/-- **Rung P2 — right derivative of the log envelope.**  `Z'` is the
threshold-Gronwall `Z'` witness for `envelopeZ`.

OBLIGATION: the differential inequality engine on the envelope carrier: the damped
`Hˢ` rate identity for the Wiener-`H³` weight — the envelope analogue of the
repo's Sobolev-side `BKMLogBootstrap` rates, carried through the PDE
(`SatisfiesNavierStokesBefore`) and the collapse `h3EnvelopeBudget_eq_iSup`. -/
def EnvelopeBudgetRightDerivative (T : ℝ) (u : VelocityEvolution) (Z' : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt (envelopeZ u) (Z' t) (Ici t) t

/-- **Rung P3 — the rate and its BKM budget.**  A continuous nonnegative rate
whose running integral stays below `M`.

OBLIGATION split: the continuity clause `ContinuousOn a (Ico 0 T)` is *exactly*
the field `BKMControl.rate_continuousOn` (`Navier/Analysis/BealeKatoMajda.lean`:
every `BKMControl` supplies a rate continuous on `[0, T)` — the hAc/hAd seats then
inherit from §2 after restriction to closed sub-horizons).  The budget clause
`∀ t ∈ Ico 0 T, ∫₀ᵗ a ≤ M` is the BKM-budget input of the damped estimate — the
same content as `NSBKMUniformVorticityAprioriAtViscosityOne`-style a priori rows
(ledger: the Clay-hard first input). -/
def EnvelopeRateBudget (a : ℝ → ℝ) (T M : ℝ) : Prop :=
  ContinuousOn a (Ico (0 : ℝ) T) ∧ (∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∫ x in (0 : ℝ)..t, a x ∂volume ≤ M)

/-- **Rung P4 — the threshold growth inequality.**  Above the threshold `Λ` the
log envelope grows at rate `a·(c + Z)`; below `Λ` nothing is assumed.

OBLIGATION: the content of `DampedThresholdGronwall.damped_rate_reduction` plus
`SobolevInterpolation` re-carried on the envelope (Wiener-`H³`) carrier — the
threshold `Λ = Λ(ν, ‖u₀‖-energy)` is the damping threshold where dissipation beats
the log-Sobolev growth, and the inequality is the engine that makes the bootstrap
*quantitative*.  This is the genuinely analytic core; the structural rungs above
(P0's base, §2's hAc/hAd seats, §4's closed side) are what this module has closed. -/
def EnvelopeDampedRateInequality (T : ℝ) (u : VelocityEvolution) (Z' a : ℝ → ℝ)
    (Λ c : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, Λ < envelopeZ u t → Z' t ≤ a t * (c + envelopeZ u t)

/-! ## 4. The bootstrap schema: closed side and base -/

/-- **Closed side.**  Under the continuity rung P1 the bootstrap's sublevel sets are
closed on every closed sub-horizon: `IsClosed.isClosed_le` against the constant. -/
theorem envelopeSublevel_isClosed {T : ℝ} {u : VelocityEvolution}
    (hP1 : EnvelopeBudgetContinuousOn T u) {T' : ℝ} (hT' : T' < T) (K : ℝ≥0∞) :
    IsClosed { t ∈ Icc (0 : ℝ) T' | h3EnvelopeBudget (u t) ≤ K } :=
  isClosed_Icc.isClosed_le
    (hP1.mono fun z hz => ⟨hz.1, lt_of_le_of_lt hz.2 hT'⟩) continuousOn_const

/-- **Nonempty base.**  Under `K ≥ h3EnvelopeBudget (u 0)` the closed sublevel set
contains the initial time — by §1's transported seed this is available at every
`K ≥ datumWeight u₀`. -/
theorem zero_in_envelopeSublevel {T' : ℝ} (hT'0 : 0 ≤ T') {u : VelocityEvolution}
    {K : ℝ≥0∞} (hK : h3EnvelopeBudget (u 0) ≤ K) :
    (0 : ℝ) ∈ { t ∈ Icc (0 : ℝ) T' | h3EnvelopeBudget (u t) ≤ K } :=
  ⟨mem_Icc.mpr ⟨le_rfl, hT'0⟩, hK⟩

/-! ## 5. The reduction bridge for P1 -/

/-- The budget of a representable slice equals the weight of any fixed representer
(the collapse `h3EnvelopeBudget_eq_iSup`, packaged for a family). -/
theorem envelopeBudget_eq_repFamilyWeight {T : ℝ} {u : VelocityEvolution}
    {a : ℝ → ES → ComplexSpace} (ha : ∀ s ∈ Ico (0 : ℝ) T, Rep (u s) (a s))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    h3EnvelopeBudget (u t) = ⨆ i : Fin 3, h3F (fun ξ => a t ξ i) :=
  h3EnvelopeBudget_eq_iSup (ha t ht)

/-- **P1 via a continuous `Rep`-family.**  The envelope's time-continuity is the
same statement as continuity of the explicit weight map of one continuous family
of representers — pointwise equality along the collapse.  This is the named route
for rung P1 in the residual list. -/
theorem envelopeBudget_continuousOn_of_repFamily (T : ℝ) (u : VelocityEvolution)
    (a : ℝ → ES → ComplexSpace)
    (ha : ∀ s ∈ Ico (0 : ℝ) T, Rep (u s) (a s))
    (hw : ContinuousOn (fun t => ⨆ i : Fin 3, h3F (fun ξ => a t ξ i)) (Ico (0 : ℝ) T)) :
    EnvelopeBudgetContinuousOn T u :=
  hw.congr fun t ht => envelopeBudget_eq_repFamilyWeight ha ht

/-! ## 6. The packaged bootstrap at a horizon, and the crown seat -/

/-- On a closed sub-horizon inside a P0 + P1 interval, the log envelope map is
continuous: `toReal` is continuous off `⊤` (`ENNReal.continuousAt_toReal`), and
`log(1 + ·)` is continuous on `[0, ∞)`. -/
theorem continuousOn_envelopeZ {T : ℝ} (u : VelocityEvolution)
    (hP0 : EnvelopeBudgetFiniteOn T u) (hP1 : EnvelopeBudgetContinuousOn T u)
    {T' : ℝ} (hT' : T' < T) : ContinuousOn (envelopeZ u) (Icc (0 : ℝ) T') := by
  have hb : ContinuousOn (fun t => h3EnvelopeBudget (u t)) (Icc (0 : ℝ) T') :=
    hP1.mono fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hT'⟩
  have hto : ContinuousOn ENNReal.toReal {x : ℝ≥0∞ | x < ⊤} :=
    ContinuousOn.mono ENNReal.continuousOn_toReal fun _x hx => hx.ne
  have hcomp := hto.comp hb fun t ht => hP0 t ⟨ht.1, lt_of_le_of_lt ht.2 hT'⟩
  refine ContinuousOn.log (ContinuousOn.add continuousOn_const hcomp) fun _t ht =>
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one ENNReal.toReal_nonneg)

/-- **The propagation rung, packaged.**  For one solution-horizon: under P0–P4,
the horizon-`T` envelope control is bounded by the T-uniform threshold-Gronwall
number built from the *base value* `envelopeZ u 0` (which §1 pins to the datum via
`envelopeBudget_init_eq_datumWeight`) and the budget `M`.  Proof: on every closed
sub-horizon `[0, T']` with `T' < T`, the log envelope map satisfies the
`threshold_gronwall_uniform` seats — `hAc`/`hAd` discharged by §2 — and the squeeze
`h3EnvelopeControl_le_iff` finishes.  This is the exact §3 bootstrap schema rung 2
of the RV3-NS sketch as a named row; its inputs are the named Props above. -/
theorem envelopeBootstrap_at_horizon {T : ℝ} (hT : 0 < T) (u : VelocityEvolution)
    {a Z' : ℝ → ℝ} {Λ c M : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ)
    (hP0 : EnvelopeBudgetFiniteOn T u) (hP1 : EnvelopeBudgetContinuousOn T u)
    (hP2 : EnvelopeBudgetRightDerivative T u Z')
    (hP3 : EnvelopeRateBudget a T M)
    (hP4 : EnvelopeDampedRateInequality T u Z' a Λ c) :
    h3EnvelopeControl T u ≤
      ENNReal.ofReal (Real.exp ((c + max (envelopeZ u 0) Λ) * Real.exp M - c) - 1) := by
  obtain ⟨haC, ha0, haM⟩ := hP3
  set B : ℝ := (c + max (envelopeZ u 0) Λ) * Real.exp M - c with hBdef
  refine (h3EnvelopeControl_le_iff u).mpr fun t ht => ?_
  set T' : ℝ := (t + T) / 2 with hTd
  have hT'pos : 0 < T' := by linarith [ht.1]
  have hT'T : T' < T := by linarith [ht.2]
  have hZc := continuousOn_envelopeZ u hP0 hP1 hT'T
  have hZd : ∀ s ∈ Ico (0 : ℝ) T',
      HasDerivWithinAt (envelopeZ u) (Z' s) (Ici s) s := fun s hs =>
    hP2 s ⟨hs.1, lt_of_lt_of_le hs.2 hT'T.le⟩
  have hAC : ContinuousOn a (Icc (0 : ℝ) T') :=
    haC.mono fun z hz => ⟨hz.1, lt_of_le_of_lt hz.2 hT'T⟩
  have hB := threshold_gronwall_uniform hc hΛ hZc hZd
    (continuousOn_runningIntegral hT'pos.le hAC)
    (fun s hs => hasDerivWithinAt_runningIntegral hT'pos.le hAC hs)
    (by simp)
    (fun s hs => ha0 s ⟨hs.1, lt_of_lt_of_le hs.2 hT'T.le⟩)
    (fun s hs => haM s ⟨hs.1, lt_of_le_of_lt hs.2 hT'T⟩)
    (fun s hs hlt => hP4 s ⟨hs.1, lt_of_lt_of_le hs.2 hT'T.le⟩ hlt)
    t ⟨ht.1, by linarith [hTd]⟩
  rw [← hBdef] at hB
  have hlt := hP0 t ht
  calc h3EnvelopeBudget (u t)
      = ENNReal.ofReal ((h3EnvelopeBudget (u t)).toReal) := (ENNReal.ofReal_toReal hlt.ne).symm
    _ ≤ ENNReal.ofReal (Real.exp (envelopeZ u t) - 1) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : Real.exp (envelopeZ u t) = 1 + (h3EnvelopeBudget (u t)).toReal := by
          unfold envelopeZ
          have h0 : 0 ≤ (h3EnvelopeBudget (u t)).toReal := ENNReal.toReal_nonneg
          rw [Real.exp_log (show (0 : ℝ) < 1 + (h3EnvelopeBudget (u t)).toReal by linarith)]
        linarith
    _ ≤ ENNReal.ofReal (Real.exp B - 1) := ENNReal.ofReal_le_ofReal (by
        have := Real.exp_le_exp.mpr hB
        linarith)

/-- **The board as one named Prop.**  A datum-level bootstrap board: thresholds
`Λ, c` and budget `M` fixed per datum, and for every horizon and every
`SolvesBefore` + `RegularOnCompacts` member from the datum, the five rungs P0–P4
with a rate and a derivative witness. -/
def EnvelopeBootstrapBoard (ν : ℝ) (u₀ : SchwartzVelocity) : Prop :=
  ∃ (Λ c M : ℝ), 0 ≤ Λ ∧ 0 ≤ c ∧ ∀ (T : ℝ), 0 < T →
    ∀ (u : VelocityEvolution) (p : PressureEvolution),
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → RegularOnCompacts T u p →
      ∃ (a Z' : ℝ → ℝ), EnvelopeRateBudget a T M ∧ EnvelopeBudgetFiniteOn T u ∧
        EnvelopeBudgetContinuousOn T u ∧ EnvelopeBudgetRightDerivative T u Z' ∧
        EnvelopeDampedRateInequality T u Z' a Λ c

/-- **The crown seat, discharged by the board.**  If every datum carries a
bootstrap board, then `APrioriIn RegularOnCompacts h3EnvelopeControl` holds — the
crown's single remaining premise is *supplied*, not assumed.  The bound depends on
the datum only through `ν`, the seed weight `datumWeight u₀` and the board numerics,
exactly the quantifier order `APrioriIn` requests (`∃ M` after `∀ u₀`). -/
theorem aprioriIn_of_envelopeBootstrapBoard
    (hboard : ∀ (ν : ℝ) (hν : 0 < ν) (u₀ : SchwartzVelocity)
      (hdiv : DivergenceFreeInitial u₀), EnvelopeBootstrapBoard ν u₀) :
    APrioriIn RegularOnCompacts h3EnvelopeControl := by
  intro ν hν u₀ hdiv
  obtain ⟨Λ, c, M, hΛ, hc, hinst⟩ := hboard ν hν u₀ hdiv
  set Z0 : ℝ := Real.log (1 + (datumWeight u₀).toReal) with hZ0def
  set B : ℝ := (c + max Z0 Λ) * Real.exp M - c with hBdef
  refine ⟨(ENNReal.ofReal (Real.exp B - 1)).toNNReal, fun T hT u p hinit hsol hR => ?_⟩
  obtain ⟨a, Z', hP3, hP0, hP1, hP2, hP4⟩ := hinst T hT u p hinit hsol hR
  have hZpin : envelopeZ u 0 = Z0 := by
    show Real.log (1 + (h3EnvelopeBudget (u 0)).toReal) = _
    rw [envelopeBudget_init_eq_datumWeight ν hν u₀ hdiv u hinit]
  have hbound := envelopeBootstrap_at_horizon hT u hc hΛ hP0 hP1 hP2 hP3 hP4
  rw [hZpin, ← hBdef] at hbound
  exact hbound.trans ((ENNReal.coe_toNNReal (a := ENNReal.ofReal (Real.exp B - 1))
    ENNReal.ofReal_ne_top).ge)

end Navier.Analysis.EnvelopePropagation

set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopePropagation.datumWeight
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopePropagation.envelopeBudget_init_lt_top
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopePropagation.envelopeBootstrap_at_horizon
#print axioms Navier.Analysis.EnvelopePropagation.envelopeBudget_init_lt_top
#print axioms Navier.Analysis.EnvelopePropagation.continuousOn_runningIntegral
#print axioms Navier.Analysis.EnvelopePropagation.hasDerivWithinAt_runningIntegral
#print axioms Navier.Analysis.EnvelopePropagation.threshold_gronwall_uniform_of_continuousRate
#print axioms Navier.Analysis.EnvelopePropagation.envelopeBudget_continuousOn_of_repFamily
#print axioms Navier.Analysis.EnvelopePropagation.envelopeSublevel_isClosed
#print axioms Navier.Analysis.EnvelopePropagation.envelopeBootstrap_at_horizon
#print axioms Navier.Analysis.EnvelopePropagation.aprioriIn_of_envelopeBootstrapBoard
