import Navier.Analysis.HorizonFreeBudgetRestart
import Navier.Analysis.EnvelopeFourierUniqueness
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The datum-level envelope seed: finiteness of `h3EnvelopeBudget` at the initial slice

**What this module lands.**  The base case of every bootstrap proof of the
crown's single remaining premise `APrioriIn RegularOnCompacts
h3EnvelopeControl` (`crown_from_envelopeApriori`,
`Navier.Analysis.HorizonFreeBudgetRestart`).  Such a bootstrap runs on the
sublevel sets `{ t | h3EnvelopeBudget (u t) ≤ K }` and needs a nonempty base:
the envelope must be finite at the initial slice, bounded by datum numerics.
This is the first quantitative leaf below the premise; the RV3-NS sketch
(2026-10-05) named it `envelopeBudget_datumSeed` and sketched its three
`have`s.  The leaf statement is the sketch's §1 verbatim.

**`h3F_lt_top_of_schwartz` (sketch `have 2`, the fresh rung).**  For *any*
Schwartz profile `T : 𝓢(ES, ℂ)`, the Fourier `H³` weight `h3F` is finite.
The repo had the weighted-`L¹` moment tower
(`fourierDatum_mom_ne_top`, via `SchwartzMap.integrable_pow_mul`) but not the
weighted-`L²` finiteness that `h3F`'s squared `ennorm` demands.  The proof
dominates pointwise: `(1 + ‖ξ‖) ^ 6 · ‖T ξ‖² ≤ 64 ‖T‖∞ · (‖T ξ‖ + ‖ξ‖^6 ‖T ξ‖)`,
where the two right-hand terms are exactly
`SchwartzMap.integrable_pow_mul 0` and `6`, so the `ENNReal` bound closes
through `Integrable.hasFiniteIntegral` and `lintegral_mono`.  No
`native_decide`, no new axioms.

**`envelopeBudget_datumSeed` (the leaf).**  For every viscosity and every
divergence-free Schwartz datum, the envelope budget of the initial velocity
field is strictly below `⊤`, and it *equals* the datum-profile weight
`M₀ := ⨆ i : Fin 3, h3F (fourierDatum ((-(2π)) • u₀) · i)` — the second
conjunct turns the seed from a bare finiteness into a usable bootstrap
constant.  Composition: `rep_base` (sketch `have 1`, the `Rep` exhibit) and
`h3EnvelopeBudget_eq_iSup` (sketch `have 3`, the budget collapse of
`EnvelopeFourierUniqueness`) squeeze finiteness over `Fin 3` from `have 2`.

**Placement note.**  The sketch designated the leaf under the
`HorizonFreeBudgetRestart` namespace, but the collapse theorem
`h3EnvelopeBudget_eq_iSup` lives in `EnvelopeFourierUniqueness.lean`, whose
line 1 imports `HorizonFreeBudgetRestart` — the designated file cannot import
it back.  This module sits downstream of both and keeps the statement
identical; the namespace is the module's own, per the repo's one-namespace-
per-file convention.

**What this does NOT claim.**  It does not prove `APrioriIn RegularOnCompacts
h3EnvelopeControl`, does not discharge the crown premise, and proves nothing
for `t > 0`: the quantifiers are single-slice datum-only (`t = 0`), with no
`∃ M ∀ T` structure — not an equivalent-premise wrapper.  What remains
crown-wide is the propagation rung of the sketch's §3 bootstrap schema:
boundedness/continuity of `t ↦ h3EnvelopeBudget (u t)` along `SolvesBefore`
members (ledger F-026: `SolvesBefore` carries no time-continuity field;
`DampedThresholdGronwall`'s `hAc`/`hAd` are supplied nowhere for the
envelope).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate BigOperators

namespace Navier.Analysis.EnvelopeDatumSeed

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.FourierMajorant
open Navier.Analysis.WienerSobolevL1
open Navier.Analysis.HorizonFreeBudgetRestart
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.EnvelopeFourierUniqueness

/-- **Weighted `L²` finiteness of a Schwartz profile** (sketch `have 2`).
If `f : ES → ℂ` is pointwise a Schwartz profile `T`, then its Fourier `H³`
weight `h3F f` is finite: `(1 + ‖ξ‖) ^ 6 · ‖f ξ‖²` is dominated pointwise by
`64 ‖T‖∞ · (‖T ξ‖ + ‖ξ‖ ^ 6 · ‖T ξ‖)`, whose two summands are integrable by
`SchwartzMap.integrable_pow_mul` (the power-`0` and power-`6` rungs). -/
theorem h3F_lt_top_of_schwartz {f : ES → ℂ} (T : SchwartzMap ES ℂ)
    (hf : ∀ ξ, f ξ = T ξ) : h3F f < ⊤ := by
  -- sup-norm bound: a Schwartz profile is a bounded continuous function.
  have hn : ∀ ξ : ES, ‖T ξ‖ ≤ ‖T.toBoundedContinuousFunction‖ := fun ξ =>
    T.toBoundedContinuousFunction.norm_coe_le_norm ξ
  set B : ℝ := ‖T.toBoundedContinuousFunction‖ with hBdef
  -- the two `integrable_pow_mul` rungs and their integrable combination
  have h0 : Integrable (fun ξ : ES => ‖T ξ‖) volume :=
    (T.integrable (μ := volume)).norm
  have h6 : Integrable (fun ξ : ES => ‖ξ‖ ^ 6 * ‖T ξ‖) volume :=
    T.integrable_pow_mul volume 6
  set D : ES → ℝ := fun ξ => (64 * B) * (‖T ξ‖ + ‖ξ‖ ^ 6 * ‖T ξ‖) with hDdef
  have hD : Integrable D volume := by
    rw [hDdef]
    exact (h0.add h6).const_mul (64 * B)
  -- Japanese-bracket polynomial squeeze, purely real arithmetic
  have hpow : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 6 ≤ 64 * (1 + t ^ 6) := by
    intro t ht
    rcases lt_trichotomy t 1 with hlt | heq | hgt
    · calc (1 + t) ^ 6 ≤ (2 : ℝ) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
        _ ≤ 64 * (1 + t ^ 6) := by norm_num; nlinarith [pow_nonneg ht 6]
    · rw [heq]
      norm_num
    · calc (1 + t) ^ 6 ≤ (2 * t) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
        _ = 64 * t ^ 6 := by ring
        _ ≤ 64 * (1 + t ^ 6) := by nlinarith [pow_nonneg ht 6]
  -- pointwise domination of the weighted square by the integrable envelope
  have hpt : ∀ ξ : ES, (1 + ‖ξ‖) ^ 6 * ‖T ξ‖ ^ 2 ≤ D ξ := by
    intro ξ
    rw [hDdef]
    have hA : (1 + ‖ξ‖) ^ 6 ≤ 64 * (1 + ‖ξ‖ ^ 6) := hpow _ (norm_nonneg _)
    have hξ : ‖T ξ‖ ≤ B := hn ξ
    calc (1 + ‖ξ‖) ^ 6 * ‖T ξ‖ ^ 2
        ≤ 64 * (1 + ‖ξ‖ ^ 6) * ‖T ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hA (pow_two_nonneg _)
      _ = (64 * (1 + ‖ξ‖ ^ 6)) * ‖T ξ‖ * ‖T ξ‖ := by ring
      _ ≤ (64 * (1 + ‖ξ‖ ^ 6)) * ‖T ξ‖ * B := mul_le_mul_of_nonneg_left hξ (by positivity)
      _ = (64 * B) * (‖T ξ‖ + ‖ξ‖ ^ 6 * ‖T ξ‖) := by ring
  unfold h3F
  have hle : (∫⁻ ξ : ES, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖f ξ‖ₑ ^ 2) ≤
      ∫⁻ ξ : ES, ‖D ξ‖ₑ := by
    refine lintegral_mono fun ξ => ?_
    calc ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖f ξ‖ₑ ^ 2
        = ENNReal.ofReal ((1 + ‖ξ‖) ^ 6 * ‖T ξ‖ ^ 2) := by
          rw [hf ξ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2,
            ← ENNReal.ofReal_mul (show 0 ≤ (1 + ‖ξ‖) ^ 6 from by positivity)]
      _ ≤ ENNReal.ofReal (D ξ) := ENNReal.ofReal_le_ofReal (hpt ξ)
      _ = ‖D ξ‖ₑ := by
          rw [hDdef, ← ofReal_norm, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
  exact lt_of_le_of_lt hle hD.hasFiniteIntegral

/-- **Datum-level envelope finiteness at the initial slice** (the seed).
For every viscosity `ν > 0` and every divergence-free Schwartz datum, the
envelope budget of the initial velocity field is strictly below `⊤`, and it
is exactly the datum-profile weight `⨆ i, h3F (fourierDatum ((-(2π)) • u₀) · i)`
— the candidate bootstrap constant `M₀`.  The base case of any bootstrap
proof of `APrioriIn RegularOnCompacts h3EnvelopeControl`; it says nothing for
`t > 0` and does not discharge the crown premise. -/
theorem envelopeBudget_datumSeed (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hdiv : DivergenceFreeInitial u₀) :
    h3EnvelopeBudget (fun x => u₀ x) < ⊤ ∧
      h3EnvelopeBudget (fun x => u₀ x) = ⨆ i : Fin 3,
        h3F (fun ξ => fourierDatum ((-(2 * Real.pi)) • u₀) ξ i) := by
  set c : SchwartzVelocity := (-(2 * Real.pi)) • u₀
  set a₀ : ES → ComplexSpace := fourierDatum c
  -- have 1 (sketch §2): the `Rep` exhibit at the initial slice
  have h1 : Rep (fun x => u₀ x) a₀ := rep_base u₀ hdiv
  -- have 2 (sketch §2): every datum-profile component weight is finite
  have h2 : ∀ i : Fin 3, h3F (fun ξ => a₀ ξ i) < ⊤ := by
    intro i
    exact h3F_lt_top_of_schwartz (𝓕 (euclidComponent c i)) (fun ξ => rfl)
  -- have 3 (sketch §2): the budget collapses to the datum profile
  have h3 : h3EnvelopeBudget (fun x => u₀ x) = ⨆ i : Fin 3, h3F (fun ξ => a₀ ξ i) :=
    h3EnvelopeBudget_eq_iSup h1
  have hsumlt : (∑ i ∈ (Finset.univ : Finset (Fin 3)), h3F (fun ξ => a₀ ξ i)) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun i _ => h2 i)
  have hsup : (⨆ i : Fin 3, h3F (fun ξ => a₀ ξ i)) < ⊤ :=
    lt_of_le_of_lt
      (iSup_le fun i =>
        Finset.single_le_sum (f := fun j => h3F (fun ξ => a₀ ξ j))
          (fun j _ => zero_le) (Finset.mem_univ i))
      hsumlt
  refine ⟨by rw [h3]; exact hsup, h3⟩

end Navier.Analysis.EnvelopeDatumSeed

set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeDatumSeed.h3F_lt_top_of_schwartz
set_option pp.fullNames true in
#check @Navier.Analysis.EnvelopeDatumSeed.envelopeBudget_datumSeed
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeDatumSeed.h3F_lt_top_of_schwartz
set_option pp.fullNames true in
#print axioms Navier.Analysis.EnvelopeDatumSeed.envelopeBudget_datumSeed
