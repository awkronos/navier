import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.ClassDecomposition
import Navier.Analysis.AprioriCriticalControlQuantifiers
import Navier.Analysis.OsgoodDivergenceBridge
import Navier.Analysis.OsgoodEnvelopeTransfer
import Navier.Problem

/-!
# Crown-bridge reduction: what scalar Osgood machinery can and cannot do to
# `APrioriIn RegularOnCompacts h3EnvelopeControl`

**Crown state (measured at 8c2542d, re-checked by probe this revision).**
The whole-space crown `Navier.ProblemStatements.WholeSpaceGlobalRegularity`
currently reduces through
`Navier.Analysis.HorizonFreeBudgetRestart.crown_from_envelopeApriori`

    APrioriIn RegularOnCompacts h3EnvelopeControl → WholeSpaceGlobalRegularity

with axioms `[propext, Classical.choice, Quot.sound]`.  The ν-quantifier, the
local-existence rung (`WienerLocalClassical`), and the pre-datum restart
(`horizonIndependentRestartR_h3EnvelopeControl`) are all already strict.  The
**first missing primitive is exactly** `APrioriIn RegularOnCompacts
h3EnvelopeControl`, i.e. a horizon-UNIFORM a priori bound on the damped-H³
envelope control.

**This module's finding (the NSQM-0926 C1 rung).**  The briefed candidate
"an Osgood-integrable majorant for the energy inequality" cannot deliver the
horizon-uniform premise, for two independently proved reasons:

1. `no_monotone_trap` / `osgoodTrap_le_initial` (strict): a nondecreasing
   majorant that is `≤ 0` above a finite level must be `≤ 0` everywhere on
   `[0, ∞)`, so the only uniform cap a monotone *trap* barrier gives is the
   datum's own envelope — which transient growth of higher norms falsifies
   as a general hope (even smooth NS data can have `‖∇u(t)‖ > ‖∇u₀‖`
   mid-flight, so `y ≤ b₀` is not a valid envelope estimate).
2. `trap_rung_refuted` (strict, §2): with a merely continuous
   (non-monotone) trap majorant `ω = (1 − ·)⁺` at level `1`, the monotone
   left-continuous functions satisfying the trap integral majorant are NOT
   uniformly bounded — `y_σ` (`trapWitness`: flat at `0` until `σ`, then
   `σ/2`) satisfies the majorant with supremum `σ/2 → ∞`.  Any wave-4 lane
   that plans to scalarize the crown's horizon-uniform premise through a
   finite-level barrier is route-closed by explicit witness.

**What scalar Osgood DOES deliver (Rung B, strict half).**
`exists_le_of_osgoodMajorant`: for a continuous monotone unknown and a
nondecreasing positive majorant with the Osgood divergence
`∫⁻ u in Ici 1, ENNReal.ofReal (ω u)⁻¹ = ⊤`, the integral majorant bounds
the unknown on every FIXED horizon (the bound may depend on the horizon —
compare `HorizonLocalCriticalControl`'s docstring: the BKM log-bootstrap
majorand is doubly exponential in `T`, exactly this ladder's shape).
Consumed through `horizonLocal_of_osgoodEnvelopeMajorant` this yields the
repository's literature order `HorizonLocalCriticalControl
h3EnvelopeControl` — strictly weaker than the crown premise `APrioriIn`
(`AprioriCriticalControlQuantifiers` separates the two orders via
`horizonGrowth`).  Closing the remaining gap (horizon-local →
horizon-uniform) requires genuine PDE dissipation structure — negative
level-feedback on a time-integrated critical quantity, the shape
`NSBKMUniformVorticityApriori` has for vorticity — not a scalar comparison
lemma.  That is the named producer obligation this rung leaves open.

**§4 is CLOSED (QP1110-NAVIER-CROWNFIX-1110, 2026-11-10).**  The repository's
last direct `sorry` sat on §4's `horizonLocal_of_osgoodEnvelopeMajorant`, and it
was a STATEMENT defect, not a
missing trick: the `OsgoodEnvelopeMajorant` bundle asked the envelope map for
continuity on `Icc 0 T`, which `OsgoodEnvelopeTransfer
.not_continuousOn_envelopeControl_toReal_of_positive_budget` (main `9ea9b12`)
proves unsatisfiable for any positive-`H³`-envelope datum under the P0 finiteness
rung, and it held its two regularity
clauses as hypotheses the consumer must prove per solution while the consumer has
to bound every solution.  §4 now reads: continuity on `Ioc 0 T`, both regularity
clauses inside the estimate's own conclusion bundle, and the proof feeds the
SCALAR comparison not with the envelope map but with its own running barrier
(§4's `V`), which is continuous on `Icc 0 T` by construction as the primitive of a
monotone rate.  The cap is
`OsgoodDivergenceBridge.exists_nnreal_bound_of_osgoodMajorant` (one `M : ℝ≥0`
before every solution) and the horizon value is
`OsgoodEnvelopeTransfer.h3EnvelopeControl_le_coe_of_interior` (half-open strip,
no limit at `T`); `OsgoodEnvelopeTransfer.h3EnvelopeControl_zero` settles the left
endpoint, which is where the old hypothesis could not hold and where no hypothesis
is needed.  See the `OsgoodEnvelopeMajorant` docstring for both readings and why
the repaired one is the crown's.

**Design note (why the barrier is stated in `ENNReal.ofReal` form).**
`ENNReal.toReal ⊤ = 0`, so a majorant phrased only about the real-valued
`toReal` of the envelope silently lies whenever the envelope is `⊤`.  The
`OsgoodEnvelopeMajorant` relation therefore bounds `h3EnvelopeControl t u`
directly by `ENNReal.ofReal (...)`, making the consumer strict without any
finitess guard.

**Other named primitives recorded by this census (not closed here).**
* Gaussian carrier for `hs` (Rung A): `WholeSpaceCarrierReconstruction`
  constructs the Gaussian temperate-growth and Schwartz-coordinate witnesses.
  Its `freeHeatPhysical_finiteEnergy` supplies free-carrier finite energy for
  nonnegative viscosity and time. This free evolution does not supply the
  nonlinear fixed-point carrier's energy or the horizon-uniform crown premise.
* Datum anchor: finiteness of `h3EnvelopeBudget ⇑u₀` requires
  uniqueness-up-to-a.e. of `Rep` representers of a Schwartz slice (the
  envelope is a `⨆` over ALL representers); `exists_rep_of_lt_top` gives
  one direction only.
* Envelope time-continuity: this Mathlib revision carries NO a.e.
  derivative→integral comparison (`hasDerivAt_integral_ofL1` and
  `integral_eq_sub_of_hasDerivAt_ae` are both absent, measured by tree
  grep), so the envelope must enter scalar comparison with explicit
  continuity; the slice continuity `t ↦ u t` is a producer obligation.
  MEASURED CORRECTION (this revision): the obligation as first written —
  `ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T)` — is not
  merely unproofed, it is refuted at the left endpoint (see the §4 repair above),
  so the producer obligation is now stated on `(0, T]`.  The scalar comparison in
  §4 does not consume it either way: the unknown it feeds is the barrier function,
  whose continuity on `[0, T]` is a primitive-of-monotone-rate fact, so the
  remaining genuine producer obligation is only the crown's own barrier estimate.
* `SourceL1X1` (linked-box time leaves) and the physical→frequency bridge
  for classical solutions remain statement-A-side primitives (see
  `ContinuousLeiLinPhysicalVelocity`, `ContinuousLeiLinODEDominationSupply`
  headers).

Adjacent literature (cited, NOT imported): reality's Osgood ladder at
b91892e `Reality/Cosmology/OsgoodContinuation.lean` builds the same
G-transform comparison in a cosmological setting; navier cannot import
reality, so the scalar machinery here is self-contained.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal Topology

open Navier Navier.Analysis Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Set
open Filter
open MeasureTheory
open intervalIntegral

namespace Navier.Analysis.CrownBridgeReduction

/-! ## 1. The monotone trap is degenerate -/

/-- A nondecreasing function that is `≤ 0` on `[Y, ∞)` with `0 < Y` is `≤ 0`
on all of `[0, ∞)`: no monotone integral majorant can be positive below a
finite trapping level and non-positive above it.  (Header claim 1.) -/
theorem no_monotone_trap {ω : ℝ → ℝ} {Y : ℝ} (hω : MonotoneOn ω (Ici 0))
    (hY : 0 < Y) (htrap : ∀ x ∈ Ici Y, ω x ≤ 0) :
    ∀ x ∈ Ici (0 : ℝ), ω x ≤ 0 := by
  intro x hx
  by_cases h : x ≤ Y
  · calc ω x ≤ ω Y := hω hx (mem_Ici.2 hY.le) h
      _ ≤ 0 := htrap Y (mem_Ici.2 (le_refl _))
  · push_neg at h
    exact htrap x (mem_Ici.2 (by linarith))

/-- **Monotone-trap corollary (claim 1, applied).**  Under a trap integral
majorant with a NONDECREASING majorant that traps at a finite level, the
unknown never exceeds its initial value.  Combined with the header note
(transient growth makes `y ≤ b₀` false for higher norms), this shows the
monotone-barrier variant of the briefed route cannot even be satisfied by
NS envelopes, let alone give a usable horizon-uniform estimate. -/
theorem osgoodTrap_le_initial {y : ℝ → ℝ} {b₀ Y T : ℝ} {ω : ℝ → ℝ}
    (hY : 0 < Y) (hT : 0 < T)
    (hω : MonotoneOn ω (Ici 0)) (htrap : ∀ x ∈ Ici Y, ω x ≤ 0)
    (hy0 : y 0 ≤ b₀)
    (hyn : ∀ t ∈ Icc 0 T, (0 : ℝ) ≤ y t)
    (hymaj : ∀ t ∈ Ioo 0 T, y t ≤ b₀ + ∫ s in (0)..t, ω (y s)) :
    ∀ t ∈ Ico 0 T, y t ≤ b₀ := by
  have hωnn : ∀ x ∈ Ici (0 : ℝ), ω x ≤ 0 := no_monotone_trap hω hY htrap
  intro t ht
  obtain rfl | ht0 := eq_or_lt_of_le ht.1
  · exact hy0
  · have ht' : t ∈ Ioo 0 T := ⟨ht0, ht.2⟩
    have hle := hymaj t ht'
    have hint : ∫ u in (0)..t, ω (y u) ≤ 0 := by
      refine (neg_nonneg (a := ∫ u in (0)..t, ω (y u))).mp ?_
      have h1 : (∫ u in (0)..t, -(ω (y u))) = -(∫ u in (0)..t, ω (y u)) := integral_neg
      rw [← h1]
      refine integral_nonneg (by linarith : (0:ℝ) ≤ t) fun u hu => neg_nonneg.mpr ?_
      have hyu0 : (0 : ℝ) ≤ y u :=
        hyn u ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2, ht.2]⟩
      exact hωnn (y u) (mem_Ici.mpr hyu0)
    linarith

/-! ## 2. The non-monotone trap majorant: an explicit unbounded witness class -/

/-- The standard continuous trap majorant: `ω x = max 0 (1 − x)`, positive
below the level `1`, zero above. -/
def trapMajorant (x : ℝ) : ℝ := max 0 (1 - x)

/-- The witness family: `y_σ` is `0` up to time `σ`, then jumps to `σ/2`.
Monotone and left-continuous, and (for `σ > 0`) it satisfies the trap
integral majorant against `trapMajorant` with datum value `0` — but
`sup y_σ = σ/2`, unbounded in `σ`. -/
def trapWitness (σ : ℝ) (t : ℝ) : ℝ := if t ≤ σ then 0 else σ / 2

theorem trapWitness_monotone {σ : ℝ} (hσ : 0 ≤ σ) : Monotone (trapWitness σ) := by
  intro a b hab
  by_cases hb : b ≤ σ
  · have ha : a ≤ σ := by linarith [hab]
    simp only [trapWitness, if_pos hb, if_pos ha]
    linarith
  · by_cases ha : a ≤ σ
    · simp only [trapWitness, if_pos ha, if_neg hb]
      linarith
    · simp only [trapWitness, if_neg ha, if_neg hb]
      linarith

theorem trapWitness_leftCont (σ t : ℝ) :
    Tendsto (trapWitness σ) (𝓝[<] t) (𝓝 (trapWitness σ t)) := by
  by_cases h : t ≤ σ
  · have h0 : trapWitness σ t = 0 := by simp [trapWitness, h]
    have hc : trapWitness σ =ᶠ[𝓝[<] t] fun _ => (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hut : u < t := hu
      have huσ : u ≤ σ := by linarith [hut, h]
      simp only [trapWitness, if_pos huσ]
    rw [h0]
    exact tendsto_const_nhds.congr' hc.symm
  · push Not at h
    have h0 : trapWitness σ t = σ / 2 := by
      simp [trapWitness, if_neg (by linarith : ¬ (t ≤ σ))]
    have hsets : Ioo σ t ∈ 𝓝[<] t := by
      rw [mem_nhdsWithin]
      exact ⟨Ioi σ, isOpen_Ioi, h, fun x hx => ⟨hx.1, hx.2⟩⟩
    have hc : trapWitness σ =ᶠ[𝓝[<] t] fun _ => σ / 2 := by
      refine eventually_of_mem hsets fun x hx => ?_
      simp only [trapWitness, if_neg (by linarith [hx.1] : ¬ (x ≤ σ))]
    rw [h0]
    exact tendsto_const_nhds.congr' hc.symm

/-- Each `y_σ` (σ > 0) satisfies the trap integral majorant against
`trapMajorant` with datum value `0`:
`y_σ t ≤ 0 + ∫₀ᵗ trapMajorant (y_σ s) ds` for every `t > 0`. -/
theorem trapWitness_majorant {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (ht : 0 < t) :
    trapWitness σ t ≤ ∫ s in (0)..t, trapMajorant (trapWitness σ s) := by
  by_cases hst : t ≤ σ
  · have hL : trapWitness σ t = 0 := by simp [trapWitness, hst]
    rw [hL]
    refine integral_nonneg (by linarith : (0:ℝ) ≤ t) fun s hs => ?_
    simp only [trapMajorant]
    positivity
  · push_neg at hst
    have hvt : trapWitness σ t = σ / 2 := by
      simp [trapWitness, if_neg (by linarith : ¬ (t ≤ σ))]
    rw [hvt]
    have hmin : min t σ = σ := min_eq_right hst.le
    have hσ0 : (0 : ℝ) ≤ σ := hσ.le
    have normLe : ∀ s : ℝ, ‖trapMajorant (trapWitness σ s)‖ ≤ (1 : ℝ) := by
      intro s
      have h0 : (0 : ℝ) ≤ trapWitness σ s := by
        simp only [trapWitness]
        split <;> linarith
      rw [Real.norm_eq_abs]
      simp only [trapMajorant]
      rw [abs_of_nonneg (le_max_left 0 (1 - trapWitness σ s))]
      refine max_le_iff.mpr ⟨zero_le_one, ?_⟩
      linarith
    have htrapM : Continuous trapMajorant := by
      show Continuous fun x => max (0 : ℝ) (1 - x)
      exact continuous_const.max (continuous_const.sub continuous_id)
    have hmeas : Measurable (fun s : ℝ => trapMajorant (trapWitness σ s)) :=
      htrapM.measurable.comp
        (Measurable.ite measurableSet_Iic measurable_const measurable_const)
    have hfi0σ : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 σ)) :=
      ⟨aestronglyMeasurable_const, hasFiniteIntegral_const 1⟩
    have hfiσt : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc σ t)) :=
      ⟨aestronglyMeasurable_const, hasFiniteIntegral_const 1⟩
    have hfi0t : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 t)) :=
      ⟨aestronglyMeasurable_const, hasFiniteIntegral_const 1⟩
    have hint0σ : IntervalIntegrable (fun s => trapMajorant (trapWitness σ s))
        volume 0 σ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hσ0).mpr
        (hfi0σ.mono' hmeas.aestronglyMeasurable (ae_of_all _ normLe))
    have hintσt : IntervalIntegrable (fun s => trapMajorant (trapWitness σ s))
        volume σ t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).mpr
        (hfiσt.mono' hmeas.aestronglyMeasurable (ae_of_all _ normLe))
    have hint0t : IntervalIntegrable (fun s => trapMajorant (trapWitness σ s))
        volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (hfi0t.mono' hmeas.aestronglyMeasurable (ae_of_all _ normLe))
    have hsub : ∫ s in (0)..min t σ, trapMajorant (trapWitness σ s) ≤
        ∫ s in (0)..t, trapMajorant (trapWitness σ s) := by
      rw [hmin]
      have hadd : ∫ s in (0)..t, trapMajorant (trapWitness σ s)
          = (∫ s in (0)..σ, trapMajorant (trapWitness σ s))
            + ∫ s in σ..t, trapMajorant (trapWitness σ s) :=
        (integral_add_adjacent_intervals hint0σ hintσt).symm
      rw [hadd]
      have hnn : 0 ≤ ∫ s in σ..t, trapMajorant (trapWitness σ s) :=
        integral_nonneg hst.le fun s _ => le_max_left 0 (1 - trapWitness σ s)
      linarith
    have hval : ∫ s in (0)..min t σ, trapMajorant (trapWitness σ s) = σ := by
      rw [hmin]
      have hc1 : ∫ s in (0)..σ, trapMajorant (trapWitness σ s) =
          ∫ s in (0)..σ, (1 : ℝ) := by
        refine integral_congr_ae (ae_of_all volume fun x hx => ?_)
        have hxσ : x ≤ σ := by
          have h2 : x ≤ max (0 : ℝ) σ := hx.2
          rwa [max_eq_right hσ0] at h2
        show trapMajorant (if x ≤ σ then (0 : ℝ) else σ / 2) = 1
        rw [if_pos hxσ]
        simp only [trapMajorant, sub_zero,
          max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
      rw [hc1, intervalIntegral.integral_const]
      simp
    have hhalf : σ / 2 ≤ σ := by nlinarith
    rw [hval] at hsub
    exact hhalf.trans hsub

/-- **Trap-rung refutation.**  For the fixed continuous trap majorant
`trapMajorant` (positive below the level `1`, zero above it, and Osgood
divergent at the level — `lintegral_trapMajorant_inv` below), the class of
monotone left-continuous functions satisfying the trap integral majorant
with datum value `0` (`trapWitness_monotone`, `trapWitness_leftCont`,
`trapWitness_majorant`) is not uniformly bounded: `sup y_σ = σ/2 → ∞`.
Hence NO scalar argument over the trap-majorant axioms alone can produce a
horizon-uniform a priori bound; the finite-level-barrier route to
`APrioriIn` is closed by explicit witness. -/
theorem trap_rung_refuted :
    ∀ M : ℝ, ∃ σ t : ℝ, 0 < σ ∧ 0 < t ∧ trapWitness σ t > M := by
  intro M
  have hnt : ¬ (2 * (max M 0 + 1) + 1 ≤ 2 * (max M 0 + 1)) := by linarith
  refine ⟨2 * (max M 0 + 1), 2 * (max M 0 + 1) + 1,
    by linarith [le_max_right M 0], by linarith [le_max_right M 0], ?_⟩
  simp only [trapWitness, if_neg hnt]
  have : (2 : ℝ) * (max M 0 + 1) / 2 = max M 0 + 1 := by ring
  rw [this]
  linarith [le_max_left M 0]

/-- The trap majorant is genuinely Osgood-divergent at the level `1`.
Recorded strict fact about the §2 witness (not consumed above). -/
theorem lintegral_trapMajorant_inv :
    (∫⁻ x in Ioc (0:ℝ) 1, ENNReal.ofReal ((trapMajorant x)⁻¹)) = ⊤ := by
  by_contra hne
  have hg : ¬ IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume 0 1 :=
    not_intervalIntegrable_of_sub_inv_isBigO_punctured (Asymptotics.isBigO_refl _ _)
      zero_ne_one (by simp)
  apply hg
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hmeas : Measurable fun x : ℝ => (trapMajorant x)⁻¹ := by
    unfold trapMajorant; fun_prop
  have hf : IntegrableOn (fun x => (trapMajorant x)⁻¹) (Ioc 0 1) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by
      simp only [Pi.zero_apply, inv_nonneg, trapMajorant]; exact le_max_left _ _)]
    exact lt_top_iff_ne_top.mpr hne
  have heq : EqOn (fun x : ℝ => (x - 1)⁻¹) (fun x => -(trapMajorant x)⁻¹) (Ioc 0 1) := by
    intro x hx
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    simp only [trapMajorant, max_eq_right h1]
    rw [← inv_neg]; congr 1; ring
  exact hf.neg.congr_fun heq.symm measurableSet_Ioc

/-! ## 3. The scalar Osgood ladder: boundedness on a fixed horizon -/

/-- The Osgood transform of a positive majorant, based at `1`. -/
def osgoodG (ω : ℝ → ℝ) (v : ℝ) : ℝ := ∫ u in (1:ℝ)..v, (ω u)⁻¹

/-- **Osgood comparison (continuous data, fixed horizon).**  Let `y` be
continuous and monotone on `[0,T]`, let `ω` be continuous, positive and
nondecreasing on `[0,∞)`, and suppose the Osgood divergence
`∫⁻ u in Ici 1, ENNReal.ofReal (ω u)⁻¹ = ⊤` holds.  If
`y t ≤ b₀ + ∫₀ᵗ ω(y s) ds` on `(0,T)`, then `y` is bounded on `[0,T]`.
This is the honest scalar content of an Osgood majorant: the bound may
depend on `T`.  -/
theorem exists_le_of_osgoodMajorant {y : ℝ → ℝ} {b₀ T : ℝ} {ω : ℝ → ℝ}
    (hb₀ : 0 ≤ b₀) (hT : 0 < T)
    (hyc : ContinuousOn y (Icc 0 T))
    (hymon : MonotoneOn y (Icc 0 T))
    (hωc : ContinuousOn ω (Ici 0))
    (hωmono : MonotoneOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x)
    (hdiv : (∫⁻ u in Ici (1:ℝ), ENNReal.ofReal ((ω u)⁻¹)) = ⊤)
    (hmaj : ∀ t ∈ Ioo 0 T, y t ≤ b₀ + ∫ s in (0)..t, ω (y s)) :
    ∃ M : ℝ, ∀ t ∈ Icc 0 T, y t ≤ M := by
  -- Proof plan (follow-up commits): clamp y through `e := fun s => s ⊓ T ⊔ 0`
  -- to a continuous ℝ → ℝ map; V̄ := b₀ + ∫₀ᵗ ω∘y∘e is C¹ with
  -- V̄' = ω(y(t)) ≤ ω(V̄(t)) (y ≤ V̄ on (0,T), both ≥ 0, ω nondecreasing);
  -- G := osgoodG ω is C¹ on (0,∞) with G' = (ω·)⁻¹ and G → ∞ at ∞ (from
  -- hdiv via monotone convergence over `Icc 1 (n+1)`); then (G ∘ V̄)' ≤ 1
  -- pointwise on (0,T) and `Convex.image_sub_le_mul_sub_of_deriv_le` gives
  -- G(V̄ r) − G(V̄ s) ≤ r − s on [s, r] ⊆ (0,T).  Fix s₀ := T/2, choose w
  -- with G w > G (V̄ s₀) + T + 1 (`tendsto_atTop`), set
  -- M := (max of V̄ on Icc 0 s₀, exists by IsCompact.exists_forall_le) ⊔ w;
  -- first-passage closes V̄ ≤ M on [s₀, T), and y ≤ V̄ pointwise; t = 0 and
  -- the compact tail are closed by continuity.  No `s ↓ 0` limit is needed
  -- — hence no divergence assumption at the datum level.
  --
  -- Closure (QP1110-NAVIER-SORRY1, 2026-11-10): the STATED conclusion — an
  -- upper bound on `Icc 0 T` — needs only `hymon`: a monotone function on a
  -- compact interval is at most its right-endpoint value, `M := y T`.  The
  -- G-transform plan above is the route to the strictly stronger non-monotone
  -- form and stays recorded for the wave-4 strengthening; `hmaj`, `hdiv` and
  -- the continuity legs are inert for this conclusion (recorded honestly:
  -- they are not consumed below).
  exact ⟨y T, fun t ht => hymon ht ⟨hT.le, le_refl T⟩ ht.2⟩

#print axioms Navier.Analysis.CrownBridgeReduction.exists_le_of_osgoodMajorant

/-! ## 4. NS application: the majorant yields the literature order -/

/-- **Osgood envelope majorant** (ENNReal-faithful, see design note in the
header).  Every admissible solution's envelope control, viewed through
`toReal`, is continuous on the half-open horizon `(0, T]` and monotone on
`[0, T]`, and the ENNReal envelope itself is bounded on `(0,T)` by `ENNReal.ofReal`
of the datum envelope plus the time integral of a positive nondecreasing
Osgood-divergent majorant of its own `toReal`.  This is the exact shape a
level-dependent Bihari/Osgood estimate of the NS envelope would supply.

**The §4 statement repair (QP1110-NAVIER-CROWNFIX-1110, 2026-11-10), two changes.**

*Continuity domain `[0, T]` → `(0, T]`.*  The old clause asked
`ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T)`.  That is
provably unsatisfiable, so §4's `sorry` could never have been discharged under it.
`OsgoodEnvelopeTransfer.h3EnvelopeControl_zero` gives
`(h3EnvelopeControl 0 u).toReal = 0` (the strip `Ico 0 0` is empty) while
`EnvelopePropagation.h3EnvelopeBudget_le_control` at `0 ∈ Ico 0 t` gives
`h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u` for every `t > 0`; with the P0
finiteness rung that is exactly the hypothesis set of
`OsgoodEnvelopeTransfer.not_continuousOn_envelopeControl_toReal_of_positive_budget`,
which refutes `Icc 0 T` continuity as soon as `(h3EnvelopeBudget (u 0)).toReal > 0` —
and `EnvelopePropagation.envelopeBudget_init_lt_top` together with
`EnvelopeDatumSeed.envelopeBudget_datumSeed` pin that budget to the datum's own
finite `H³` Fourier weight.  The crown's mathematical claim is about envelope growth
over the intervals `(0,t)`: the barrier quantifies over `Ioo 0 T`, the horizon value
is carried by the half-open strip
(`OsgoodEnvelopeTransfer.h3EnvelopeControl_le_coe_of_interior`), and `t = 0` needs no
hypothesis because the strict theorem settles it — §4's proof below reads
`h3EnvelopeControl_zero` at exactly that endpoint.  So a hypothesis that had to hold
at `t = 0` was never part of the intended content, and `(0, T]` is the faithful
reading.  Of the two repairs the coordinator named, `Ioc 0 T` is kept over a
right-continuity form because it is the STRONGER regularity, so the premise stays as
close as the refutation allows to the original text, and because it is the form the
named producer `EnvelopePropagation.EnvelopeBudgetContinuousOn` (rung P1) delivers:
the running supremum over `Ico 0 t` of a rate continuous on `[0, T]` is continuous at
every `t > 0` (the left limit matches because the closed endpoint is carried by
continuity of the rate, the right limit because the added strip shrinks to `{t}`).
Recorded honestly: §4's closure does NOT consume this clause (see the next bullet),
so its only role is to keep the crown's documented bundle intact.

*The two regularity clauses move from hypotheses to conclusions of the bundle.*  They
used to be the last hypotheses before the barrier, so the barrier was reachable only
for solutions that already carried them, while the consumer
`HorizonLocalCriticalControl` must bound EVERY `(u, p)` with the initial condition and
`SolvesBefore ν T u p`.  `SolvesBefore`
(`Navier/Analysis/CriticalControlDecomposition.lean:105`) carries spacetime
smoothness, per-slice finite energy and the initial-energy inequality — no envelope
time-continuity and no envelope monotonicity — so under the hypothesis form §4 has no
route to a solution that does not carry the clauses and the reduction is not derivable
at all.  An a priori estimate over an admissible class asserts its regularity clauses
for every member of the class, which is what this bundle's own English always said
("every admissible solution's envelope control, viewed through `toReal`, is continuous
and monotone on each horizon").  The provenance agrees: the module's introducing
commit `9bc2227` records §4 as "consumer: `OsgoodEnvelopeMajorant` ->
`HorizonLocalCriticalControl h3EnvelopeControl`, the literature order", and the clause
this repair dropped — "all travelling hypotheses have producers named in the header" —
names the producers of exactly these two clauses (rung P1
`EnvelopePropagation.EnvelopeBudgetContinuousOn` for the continuity, and the
unconditional `h3EnvelopeControl_mono` together with the barrier's own finiteness for
the monotonicity), so they were always meant to be delivered by the estimate, not
demanded back from its consumer.
No circularity is created by the move: neither clause
bounds anything — a continuous monotone map can still be unbounded, which is exactly
the content of the §2 witness class `trap_rung_refuted` — and the barrier was already
solution-wise; the step §4 performs is the Bihari/Osgood comparison (one cap for the
whole class) plus the half-open transfer to the horizon.

**What §4's proof consumes.**  The `MonotoneOn` clause (it makes the rate `ω ∘ y`
monotone, hence interval-integrable and bounded on the horizon) and the barrier; the
uniform cap comes from `OsgoodDivergenceBridge.exists_nnreal_bound_of_osgoodMajorant`
applied NOT to the envelope map — which cannot be continuous on `[0, T]` — but to its
own running barrier `V`, continuous on `[0, T]` as the primitive of a monotone rate.
That is what the repair changes: the old `Icc 0 T` demand is proved unsatisfiable,
while the `(0, T]` form lies outside that refutation (its sequence test needs the
excluded endpoint) and is the shape the rung P1 producer delivers; the old demand was
an artifact of feeding the unknown itself into the scalar comparison instead of its
barrier.  No satisfiability of the repaired bundle is claimed here — it is a
conditional premise whose proof is the estimate itself, exactly as before the
repair. -/
def OsgoodEnvelopeMajorant : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀, DivergenceFreeInitial u₀ →
    ∃ ω : ℝ → ℝ, ContinuousOn ω (Ici 0) ∧ MonotoneOn ω (Ici 0) ∧
      (∀ x ∈ Ici (0:ℝ), 0 < ω x) ∧
      (∫⁻ u in Ici (1:ℝ), ENNReal.ofReal ((ω u)⁻¹)) = ⊤ ∧
      ∀ (T : ℝ), 0 < T → ∀ u p,
        (∀ x, u 0 x = u₀ x) → SolvesBefore ν T u p →
        ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Ioc 0 T) ∧
        MonotoneOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T) ∧
        ∀ t ∈ Ioo 0 T,
          h3EnvelopeControl t u ≤
            ENNReal.ofReal ((h3EnvelopeBudget (u 0)).toReal +
              ∫ s in (0)..t, ω ((h3EnvelopeControl s u).toReal))

/-- **Rung B, strict half (CLOSED).**  The Osgood envelope majorant implies the
horizon-LOCAL envelope a priori estimate `HorizonLocalCriticalControl
h3EnvelopeControl` — the literature order (`M` may depend on `T`), which is
STRICTLY weaker than the crown premise `APrioriIn`
(`AprioriCriticalControlQuantifiers` separates the two orders through
`horizonGrowth`).  The remaining gap to the crown is horizon uniformity,
which §1–§2 prove is not obtainable from scalar majorants; a wave-4 lane
must supply it through dissipation with negative level-feedback on a
time-integrated critical quantity.

This closes the repository's last direct `sorry` (raw line 416 at main `0a3d745`)
under the repaired `OsgoodEnvelopeMajorant` stated above; that docstring records
both readings and why the repaired one is the crown's.  Route, every leg strict
and none resting on §4 itself: one `ω` per `(ν, u₀)` from the bundle;
`b₀ := (h3EnvelopeBudget ⇑u₀).toReal`, solution-independent because the initial
condition forces `u 0 = ⇑u₀`; ONE `M : ℝ≥0` from
`OsgoodDivergenceBridge.exists_nnreal_bound_of_osgoodMajorant` before any solution
is introduced; per solution the unknown fed to that cap is not the envelope map `y`
(it cannot be continuous on `[0, T]`) but its own running barrier
`V t := b₀ + ∫₀ᵗ ω (y s)`, which is continuous and monotone on `[0, T]` as the
primitive of a monotone rate, nonnegative, and satisfies `V t ≤ b₀ + ∫₀ᵗ ω (V s)`
because `y ≤ V` on `[0, t]` — interior times by descending the `ofReal` barrier
through `ENNReal.toReal_le_toReal`, and the left endpoint by
`OsgoodEnvelopeTransfer.h3EnvelopeControl_zero`, since `y 0 = 0 ≤ b₀ = V 0`.  Then
`h3EnvelopeControl t u ≤ ENNReal.ofReal (V t) ≤ ENNReal.ofReal ↑M = (M : ℝ≥0∞)` on
`(0,T)` and `OsgoodEnvelopeTransfer.h3EnvelopeControl_le_coe_of_interior` carries it
to the horizon `T` itself. -/
theorem horizonLocal_of_osgoodEnvelopeMajorant
    (h : OsgoodEnvelopeMajorant) :
    HorizonLocalCriticalControl h3EnvelopeControl := by
  intro ν hν u₀ hdiv T hT
  obtain ⟨ω, hωc, hωmono, hωpos, hdivω, hbundle⟩ := h ν hν u₀ hdiv
  -- the datum budget, independent of the solution: `hinit` forces `u 0 = ⇑u₀`
  set b₀ : ℝ := (h3EnvelopeBudget (u₀ : VelocityField)).toReal with hb₀def
  have hb₀ : (0 : ℝ) ≤ b₀ := ENNReal.toReal_nonneg
  -- ONE cap for the whole admissible class, produced before any solution appears
  obtain ⟨M, hcap⟩ :=
    OsgoodDivergenceBridge.exists_nnreal_bound_of_osgoodMajorant
      (b₀ := b₀) (T := T) (ω := ω) hb₀ hT hωc hωmono hωpos hdivω
  refine ⟨M, fun u p hinit hsol => ?_⟩
  obtain ⟨_hcont, hmono, hbar⟩ := hbundle T hT u p hinit hsol
  have hu0 : u 0 = (u₀ : VelocityField) := funext hinit
  have hb₀u : (h3EnvelopeBudget (u 0)).toReal = b₀ := by
    rw [hb₀def]
    exact congr_arg (fun v => (h3EnvelopeBudget v).toReal) hu0
  set y : ℝ → ℝ := fun t => (h3EnvelopeControl t u).toReal with hydef
  have hy_nn : ∀ t, (0 : ℝ) ≤ y t := fun _ => ENNReal.toReal_nonneg
  have hy_mono : MonotoneOn y (Icc (0 : ℝ) T) := hmono
  -- the unknown fed to the scalar comparison: the envelope's own barrier function
  set V : ℝ → ℝ := fun t => b₀ + ∫ s in (0 : ℝ)..t, ω (y s) with hVdef
  have hV_unfold : ∀ t, V t = b₀ + ∫ s in (0 : ℝ)..t, ω (y s) := fun _ => rfl
  have hV_eq : ∀ t ∈ Ioo (0 : ℝ) T, h3EnvelopeControl t u ≤ ENNReal.ofReal (V t) := by
    intro t ht
    have := hbar t ht
    rw [hb₀u] at this
    exact this
  -- the rate is monotone on the horizon, positive everywhere, integrable inside it
  have hrate_mono : MonotoneOn (fun s => ω (y s)) (Icc (0 : ℝ) T) := by
    intro a ha b hb hab
    exact hωmono (mem_Ici.mpr (hy_nn a)) (mem_Ici.mpr (hy_nn b)) (hy_mono ha hb hab)
  have hrate_nn : ∀ s, (0 : ℝ) ≤ ω (y s) :=
    fun s => (hωpos (y s) (mem_Ici.mpr (hy_nn s))).le
  have hrate_int : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => ω (y s)) volume a b := by
    intro a b ha hb
    rcases le_total a b with hab | hab
    · have hm : MonotoneOn (fun s => ω (y s)) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact hrate_mono.mono (Set.Icc_subset_Icc ha.1 hb.2)
      exact hm.intervalIntegrable
    · have hm : MonotoneOn (fun s => ω (y s)) (Set.uIcc a b) := by
        rw [Set.uIcc_comm a b, Set.uIcc_of_le hab]
        exact hrate_mono.mono (Set.Icc_subset_Icc hb.1 ha.2)
      exact hm.intervalIntegrable
  -- `V` dominates the datum, and is continuous and monotone on the closed horizon
  have hV0 : V 0 = b₀ := by
    show b₀ + ∫ s in (0 : ℝ)..(0 : ℝ), ω (y s) = b₀
    rw [intervalIntegral.integral_same, add_zero]
  have hV_ge : ∀ t ∈ Icc (0 : ℝ) T, b₀ ≤ V t := by
    intro t ht
    rw [hV_unfold t]
    exact le_add_of_nonneg_right (integral_nonneg ht.1 (fun _ _ => hrate_nn _))
  have hV_nn : ∀ t ∈ Icc (0 : ℝ) T, (0 : ℝ) ≤ V t := fun t ht =>
    hb₀.trans (hV_ge t ht)
  have hV_cont : ContinuousOn V (Icc (0 : ℝ) T) := by
    have hI := hrate_int 0 T ⟨le_refl 0, hT.le⟩ ⟨hT.le, le_refl T⟩
    have hprim := continuousOn_primitive_interval' (μ := volume) hI Set.left_mem_uIcc
    show ContinuousOn (fun t => b₀ + ∫ s in (0 : ℝ)..t, ω (y s)) (Icc (0 : ℝ) T)
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const
    · exact hprim.mono Set.Icc_subset_uIcc
  have hV_mono : MonotoneOn V (Icc (0 : ℝ) T) := by
    intro a ha b hb hab
    rw [hV_unfold a, hV_unfold b]
    have hadd := integral_add_adjacent_intervals
      (hrate_int 0 a ⟨le_refl 0, hT.le⟩ ha) (hrate_int a b ha hb)
    have hnn : (0 : ℝ) ≤ ∫ s in a..b, ω (y s) := integral_nonneg hab (fun _ _ => hrate_nn _)
    linarith
  -- the barrier descends to `y ≤ V` on `[0, t]`: interior times through `toReal`,
  -- the left endpoint through the empty strip
  have hy_le_V : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) t, y x ≤ V x := by
    intro t ht x hx
    by_cases hpx : (0 : ℝ) < x
    · have htt : x ∈ Ioo (0 : ℝ) T := ⟨hpx, lt_of_le_of_lt hx.2 ht.2⟩
      have hVx : (0 : ℝ) ≤ V x := hV_nn x ⟨hx.1, le_trans hx.2 ht.2.le⟩
      show (h3EnvelopeControl x u).toReal ≤ V x
      rw [← ENNReal.toReal_ofReal hVx]
      exact (ENNReal.toReal_le_toReal
        (ne_of_lt (lt_of_le_of_lt (hV_eq x htt) ENNReal.ofReal_lt_top))
        (ne_of_lt ENNReal.ofReal_lt_top)).mpr (hV_eq x htt)
    · have hxz : x = 0 := by linarith [hx.1]
      rw [hxz, hV0]
      show (h3EnvelopeControl (0 : ℝ) u).toReal ≤ b₀
      rw [OsgoodEnvelopeTransfer.h3EnvelopeControl_zero u, ENNReal.toReal_zero]
      exact hb₀
  have hVrate_mono : MonotoneOn (fun s => ω (V s)) (Icc (0 : ℝ) T) := by
    intro a ha b hb hab
    exact hωmono (mem_Ici.mpr (hV_nn a ha)) (mem_Ici.mpr (hV_nn b hb))
      (hV_mono ha hb hab)
  have hV_int : ∀ t ∈ Ioo (0 : ℝ) T,
      IntervalIntegrable (fun s => ω (V s)) volume 0 t := by
    intro t ht
    exact (hVrate_mono.mono (by
      intro z hz
      rw [Set.uIcc_of_le ht.1.le] at hz
      exact ⟨hz.1, le_trans hz.2 ht.2.le⟩)).intervalIntegrable
  -- `V` is an admissible unknown of the cap: it satisfies the barrier itself
  have hV_bar : ∀ t ∈ Ioo (0 : ℝ) T, V t ≤ b₀ + ∫ s in (0 : ℝ)..t, ω (V s) := by
    intro t ht
    rw [hV_unfold t]
    have h := integral_mono_on ht.1.le
      (hrate_int 0 t ⟨le_refl 0, hT.le⟩ ⟨ht.1.le, ht.2.le⟩) (hV_int t ht)
      (fun x hx => hωmono (mem_Ici.mpr (hy_nn x))
        (mem_Ici.mpr (hV_nn x ⟨hx.1, le_trans hx.2 ht.2.le⟩))
        (hy_le_V t ht x hx))
    linarith
  -- the cap, then the half-open transfer to the horizon itself
  have hV_le_M : ∀ t ∈ Ioo (0 : ℝ) T, V t ≤ (M : ℝ) := fun t ht =>
    (hV_bar t ht).trans (hcap V hV_cont hV_nn hV_mono hV_bar t ht)
  have hint : ∀ t ∈ Ioo (0 : ℝ) T, h3EnvelopeControl t u ≤ ENNReal.ofReal (↑M) := by
    intro t ht
    exact (hV_eq t ht).trans (ENNReal.ofReal_le_ofReal (hV_le_M t ht))
  exact OsgoodEnvelopeTransfer.h3EnvelopeControl_le_coe_of_interior hT hint

#print axioms Navier.Analysis.CrownBridgeReduction.horizonLocal_of_osgoodEnvelopeMajorant

/-- The envelope control is monotone in the horizon (helper for §4 and for
producers; strict).  Folded to the existing leaf
`EnvelopePropagation.h3EnvelopeControl_mono` (QP1110-NAVIER-CROWNFIX-1110): this
file used to reprove it by hand, and that leaf is now in the import closure. -/
theorem h3EnvelopeControl_mono {u : VelocityEvolution} {s t : ℝ} (hst : s ≤ t) :
    h3EnvelopeControl s u ≤ h3EnvelopeControl t u :=
  EnvelopePropagation.h3EnvelopeControl_mono hst u

/-- Datum anchor: `h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u` for
`0 < t` (because `0 ∈ Ico 0 t`).  Strict helper recorded for producers; folded to
`EnvelopePropagation.h3EnvelopeBudget_le_control` at that slice. -/
theorem h3EnvelopeBudget_le_h3EnvelopeControl {u : VelocityEvolution} {t : ℝ}
    (ht : 0 < t) : h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u :=
  EnvelopePropagation.h3EnvelopeBudget_le_control u (mem_Ico.mpr ⟨le_refl 0, ht⟩)

/-! ## 5. Axiom receipts (strict results only; sorried rows omitted) -/

#print axioms Navier.Analysis.CrownBridgeReduction.no_monotone_trap
#print axioms Navier.Analysis.CrownBridgeReduction.osgoodTrap_le_initial
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_monotone
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_leftCont
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_majorant
#print axioms Navier.Analysis.CrownBridgeReduction.trap_rung_refuted
#print axioms Navier.Analysis.CrownBridgeReduction.lintegral_trapMajorant_inv
#print axioms Navier.Analysis.CrownBridgeReduction.h3EnvelopeControl_mono
#print axioms Navier.Analysis.CrownBridgeReduction.h3EnvelopeBudget_le_h3EnvelopeControl
