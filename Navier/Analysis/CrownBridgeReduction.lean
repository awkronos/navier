import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.ClassDecomposition
import Navier.Analysis.AprioriCriticalControlQuantifiers
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

**Design note (why the barrier is stated in `ENNReal.ofReal` form).**
`ENNReal.toReal ⊤ = 0`, so a majorant phrased only about the real-valued
`toReal` of the envelope silently lies whenever the envelope is `⊤`.  The
`OsgoodEnvelopeMajorant` relation therefore bounds `h3EnvelopeControl t u`
directly by `ENNReal.ofReal (...)`, making the consumer strict without any
finitess guard.

**Other named primitives recorded by this census (not closed here).**
* Gaussian carrier for `hs` (Rung A):
  `freeHeatPhysical_finiteEnergy_of_schwartz`
  (WholeSpaceCarrierReconstruction) needs exactly
  `∀ i, ∃ g : SchwartzMap ES ℂ, physicalCoord (freeHeatTraj ν u₀ t) i = ⇑g`.
  Measured at this revision: `Function.HasTemperateGrowth` and the bilinear
  Schwartz-pairing CLMs exist, but there is NO Gaussian-as-`SchwartzMap`
  API and the iterated-Fréchet-derivative bounds are real work — the "one
  Mathlib entry away" comment there is too optimistic and is not repeated.
* Datum anchor: finiteness of `h3EnvelopeBudget ⇑u₀` requires
  uniqueness-up-to-a.e. of `Rep` representers of a Schwartz slice (the
  envelope is a `⨆` over ALL representers); `exists_rep_of_lt_top` gives
  one direction only.
* Envelope time-continuity `ContinuousOn (fun t => (h3EnvelopeControl t u)
  .toReal) (Icc 0 T)`: this Mathlib revision carries NO a.e.
  derivative→integral comparison (`hasDerivAt_integral_ofL1` and
  `integral_eq_sub_of_hasDerivAt_ae` are both absent, measured by tree
  grep), so the envelope must enter scalar comparison with explicit
  continuity; the slice continuity `t ↦ u t` is a producer obligation.
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
    (∫⁻ x in Ioc (0:ℝ) 1, ENNReal.ofReal ((trapMajorant x)⁻¹)) = ⊤ :=
  by sorry

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
  sorry

/-! ## 4. NS application: the majorant yields the literature order -/

/-- **Osgood envelope majorant** (ENNReal-faithful, see design note in the
header).  Every admissible solution's envelope control, viewed through
`toReal`, is continuous and monotone on each horizon, and the ENNReal
envelope itself is bounded on `(0,T)` by `ENNReal.ofReal` of the datum
envelope plus the time integral of a positive nondecreasing
Osgood-divergent majorant of its own `toReal`.  All travelling hypotheses
have producers named in the header.  This is the exact shape a
level-dependent Bihari/Osgood estimate of the NS envelope would supply. -/
def OsgoodEnvelopeMajorant : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀, DivergenceFreeInitial u₀ →
    ∃ ω : ℝ → ℝ, ContinuousOn ω (Ici 0) ∧ MonotoneOn ω (Ici 0) ∧
      (∀ x ∈ Ici (0:ℝ), 0 < ω x) ∧
      (∫⁻ u in Ici (1:ℝ), ENNReal.ofReal ((ω u)⁻¹)) = ⊤ ∧
      ∀ (T : ℝ), 0 < T → ∀ u p,
        (∀ x, u 0 x = u₀ x) → SolvesBefore ν T u p →
        ContinuousOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T) →
        MonotoneOn (fun t => (h3EnvelopeControl t u).toReal) (Icc 0 T) →
        ∀ t ∈ Ioo 0 T,
          h3EnvelopeControl t u ≤
            ENNReal.ofReal ((h3EnvelopeBudget (u 0)).toReal +
              ∫ s in (0)..t, ω ((h3EnvelopeControl s u).toReal))

/-- **Rung B, strict half.**  The Osgood envelope majorant implies the
horizon-LOCAL envelope a priori estimate `HorizonLocalCriticalControl
h3EnvelopeControl` — the literature order (`M` may depend on `T`), which is
STRICTLY weaker than the crown premise `APrioriIn`
(`AprioriCriticalControlQuantifiers` separates the two orders through
`horizonGrowth`).  The remaining gap to the crown is horizon uniformity,
which §1–§2 prove is not obtainable from scalar majorants; a wave-4 lane
must supply it through dissipation with negative level-feedback on a
time-integrated critical quantity. -/
theorem horizonLocal_of_osgoodEnvelopeMajorant
    (h : OsgoodEnvelopeMajorant) :
    HorizonLocalCriticalControl h3EnvelopeControl := by
  -- Proof plan: ν, u₀ ⟹ ω.  Fix T, solution u, p with init + SolvesBefore.
  -- y := (fun t => (h3EnvelopeControl t u).toReal); b₀ := (h3EnvelopeBudget
  -- (u 0)).toReal ≥ 0.  The toReal majorant descends from the ofReal
  -- barrier: y t ≤ (ofReal ·).toReal = the real bound (barrier RHS < ⊤).
  -- exists_le_of_osgoodMajorant ⟹ |y| ≤ M₀ on Icc 0 T.  Transfer: for
  -- t ∈ Ico 0 T, h3EnvelopeBudget (u t) ≤ h3EnvelopeControl t' u for some
  -- t' ∈ Ico 0 T (e.g. (t+T)/2) ≤ ENNReal.ofReal M₀; taking the sup over
  -- t gives h3EnvelopeControl T u ≤ ENNReal.ofReal M₀ ≤ ⌈M₀⌉₊, which is
  -- exactly the HorizonLocal conclusion.
  sorry

/-- The envelope control is monotone in the horizon (helper for §4 and for
producers; strict). -/
theorem h3EnvelopeControl_mono {u : VelocityEvolution} {s t : ℝ} (hst : s ≤ t) :
    h3EnvelopeControl s u ≤ h3EnvelopeControl t u := by
  unfold h3EnvelopeControl
  refine iSup_le fun a => iSup_le fun ha => ?_
  have haT : a ∈ Ico 0 t := by
    obtain ⟨h1, h2⟩ := ha
    exact ⟨h1, by linarith [hst]⟩
  exact le_trans (le_iSup (fun _ : a ∈ Ico 0 t => h3EnvelopeBudget (u a)) haT)
    (le_iSup (fun k => ⨆ _ : k ∈ Ico 0 t, h3EnvelopeBudget (u k)) a)

/-- Datum anchor: `h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u` for
`0 < t` (because `0 ∈ Ico 0 t`).  Strict helper recorded for producers. -/
theorem h3EnvelopeBudget_le_h3EnvelopeControl {u : VelocityEvolution} {t : ℝ}
    (ht : 0 < t) : h3EnvelopeBudget (u 0) ≤ h3EnvelopeControl t u := by
  unfold h3EnvelopeControl
  have h0 : (0 : ℝ) ∈ Ico 0 t := mem_Ico.mpr ⟨le_refl _, ht⟩
  exact le_trans (le_iSup (fun _ : (0:ℝ) ∈ Ico 0 t => h3EnvelopeBudget (u 0)) h0)
    (le_iSup (fun k => ⨆ _ : k ∈ Ico 0 t, h3EnvelopeBudget (u k)) 0)

/-! ## 5. Axiom receipts (strict results only; sorried rows omitted) -/

#print axioms Navier.Analysis.CrownBridgeReduction.no_monotone_trap
#print axioms Navier.Analysis.CrownBridgeReduction.osgoodTrap_le_initial
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_monotone
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_leftCont
#print axioms Navier.Analysis.CrownBridgeReduction.trapWitness_majorant
#print axioms Navier.Analysis.CrownBridgeReduction.trap_rung_refuted
#print axioms Navier.Analysis.CrownBridgeReduction.h3EnvelopeControl_mono
#print axioms Navier.Analysis.CrownBridgeReduction.h3EnvelopeBudget_le_h3EnvelopeControl
