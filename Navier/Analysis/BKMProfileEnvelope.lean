/-
Original work, lane L6b5, 2026-09-14.
-/
import Navier.Analysis.BKMProfileRateBound
import Navier.Construction.PhysicalWaveSum
import Navier.Construction.SimilarityCoordinates

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators ContDiff
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Analysis.BKMProfileGronwallPair
open Navier.Analysis.BKMProfileRateBound
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate
open Navier.Construction.PhysicalWaveSum

/-!
# The selected-profile envelope bridge: spatial-uniform `physicalQ` vorticity
# bounds and the coordinate comparison that feeds the sandwich bridges

## The selected profile, identified

At `b6337b2` the single surviving scalar leaf of the BKM residual for the
selected forced profile is `VorticityRateBound u`
(`BKMProfileGronwallPair.lean:109`), reduced by `BKMProfileRateBound`
(`.lean:178/:355`) to either of two envelopes on the peak-vorticity profile
`V u t = ⨆ x, officialEuclideanNorm (vorticity (uncurry u) t x)`
(`BKMVorticityIntegralDivergence.lean:246`).

The concrete selected `u` consumed by the chain is not a free-standing global
`def`; it is the velocity slot of the `R3CompactCandidate.Properties`
competitor produced by the witness chain

- `Navier/Construction/ActualCandidateAssembly.lean:1184` `selected_witness :
  Witness selectedBudget selectedThreshold …` (`:1160` `witness`, `:1128`
  `Witness`), which exhibits a schedule `a : ℕ → ℕ` and staged sums
  `ASum = SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
  (physicalQ F.data.h) (potentialStages B N0 hN)`
  (`ActualCandidateAssembly.lean:538`: stage 0 is
  `zerothPotential = TailGaugePotential.finalPotential H v upper B ∘ …`, the
  modulated slow base plus initialization; stages `j ≥ 1` are
  `positivePotential` corrections),
- wrapped by `R3CompactCandidate.of_localized_fields`
  (`R3CompactCandidate.lean:254`), whose `Properties` velocity is
  `R3CompactCandidate.velocity ASum BSum =
  TimeLocalization.activatedVelocity (fun z => cutVelocity ASum z +
  cutPotential BSum z)` (`R3CompactCandidate.lean:211`), the whole-space
  localized version of the periodic local model
  `periodicVelocity ASum BSum` (`:214`), equal to it on the inner cube.

So the selected `u` is **base + cascade corrections**, activated in time and
cut in space; the modulated slow base `FinalSlowBase.velocity H v upper B`
(`FinalSlowBase.lean:281`) is stage 0 of the sum, not the whole profile. The
staged-cascade mechanism data: gains `ActualIterationLedger.gain h j = h * j /
10` (`ActualIterationLedger.lean:38`) with `Tendsto gain atTop atTop`, and
stage accuracies `sigma J = 1/5 + J/10` (`ExponentLedger.lean:293`).

## What this module proves

The quantitative layer of the repository states every assembled-field estimate
in the similarity coordinate `physicalQ h (t, x)` over ALL space
(`CutStageEstimates.RawStageBounds`, `SolenoidalDiagonal.potentialSum`,
`full_sum_zero_of_sublevel_le`), while the sandwich bridges of
`BKMProfileRateBound` consume the profile `V u` against the physical time
factor `(1 - t)^(-α)`. The bridge between these two native formats is the
coordinate comparison

    1 - t ≤ physicalQ h (t, x)          (everywhere, `t < 1`),
    physicalQ h (t, 0) = 1 - t           (equality on the symmetry axis),

proved here as `one_sub_le_physicalQ` and `physicalQ_axis` from
`SimilarityCoordinates.coordinateQ_spec`
(`forwardScalar a z q = q - z² · q^a ≤ q`). No such comparison existed in the
repo.

`vorticityRateBound_of_q_curlBound` then converts a spatially-uniform
`physicalQ`-power upper bound on the pointwise vorticity, plus an axis-point
lower bound of the same power, into the named leaf via the sandwich bridge.
The hypotheses are strictly stronger than the sandwich hypotheses (the upper
bound is pointwise in `x` in the format the stage machinery actually emits,
and the lower bound is a pointwise axis value, not already a sup); they are
not a restatement of the conclusion. The downstream corollaries
`gronwall_pair_of_q_curlBound`,
`vorticity_integral_divergence_of_q_curlBound`,
`lintegral_vorticity_integral_divergence_of_q_curlBound` consume
`gronwall_pair_of_rate_bound`, `vorticity_integral_divergence_of_rate_bound`,
`lintegral_vorticity_integral_divergence_of_rate_bound`.

## Exact surviving proposition (OPEN)

This module does NOT discharge `VorticityRateBound` for the selected `u`.
Neither envelope hypothesis of `BKMProfileRateBound` is instantiated by any
theorem currently in the repo, for any competitor: `grep` shows no `V u t ≤`,
no curl-norm bound at the assembled (`velocity`/`periodicVelocity`/
`potentialSum`) level — the quantitative layer stops at
`StageEstimates.potential_bound : RawStageBounds …`
(`MixedCandidateAssembly.lean:36`, `1 ≤ j` only) and axis-filter germs
(`DiagonalResidual.JetRate` in `finite_background`). Closing the leaf for the
selected `u` needs the following named transports (lane brief route (a)+(b));
the axis facts for the stage-0 base are supplied by sibling lane L6b4
(`/tmp/navier-l6b4/Navier/Construction/BaseVorticityAxis.lean`,
`axis_vorticity_origin`, exponent `A h + 1/2 = 1 + h > 1` by
`CoordinateAlgebra.lean:27`):

1. positive-stage sum bound: from `ThreeCutBounds`
   (`MixedDiagonalSchedule.lean:146/237`, schedule-chosen) to a uniform
   jet bound on `potentialSum` over `positiveStages` on `preterminal`
   (the per-stage `RawStageBounds` exist; the schedule summation over `j`
   does not),
2. stage-0 bound: the same for `cutStage … A 0` from the base estimate
   (`ActualPhysicalStageBounds` "initialized velocity estimate"),
3. curl transport: `vorticity (uncurry …)` of the assembled field ≤ a
   constant times the `m = 1` jet bound (`PhysicalClassBounds.lean`
   `physical_vector_curl_jet_bound` covers `PhysicalWaveSum.vectorSum`,
   not the assembled sums),
4. cut + activation: `R3CompactCandidate.velocity` equals the raw sum on
   `[3/4, 1)` (`timeSwitch_one_of_three_quarters_le`) and vanishes off
   `supportCylinder`, so the spatial sup of the cut field is the sup of
   the sum on the cylinder,
5. axis lower bound for the FULL u: corrections' axis jets must be shown to
   be dominated at `x = 0` by the base term (the positive-axis vanishing
   mechanism `EntranceAlignedBase.modulated_positive_axis` exists for the
   base's own Borel sum; nothing yet for the `initial` part, the
   `SolenoidalDiagonal` projection, or the periodization/activation).

With 1–4 the upper envelope `hup` below is instantiable; with 5 the axis
envelope `haxis` is. Until then the crown `∃`-theorems of
`BKMForcedBreakdownNecessity`/`ConstructedFiniteTimeObstruction` remain
unchanged: this module makes NO declaration unconditional.
-/

namespace Navier.Analysis.BKMProfileEnvelope

private abbrev ESpace := Navier.Construction.ProblemStatement.Space

/-! ## 1. The coordinate comparison. -/

/-- The forward similarity scalar satisfies `forwardScalar a z q ≤ q`:
`q - z² · q^a ≤ q` for every real `a`, `z`, and `q ≥ 0`. -/
theorem forwardScalar_le_self {a z q : ℝ} (hq : 0 ≤ q) :
    Navier.Construction.SimilarityCoordinates.forwardScalar a z q ≤ q := by
  have h : 0 ≤ z ^ 2 * q ^ a :=
    mul_nonneg (sq_nonneg z) (Real.rpow_nonneg hq a)
  have h2 : Navier.Construction.SimilarityCoordinates.forwardScalar a z q =
      q - z ^ 2 * q ^ a := rfl
  rw [h2]; linarith

/-- The similarity `q`-coordinate dominates the remaining time: for
`0 < h < 1/2`, `t < 1`, and every physical point `(t, y)`,
`1 - t ≤ physicalQ h (t, y)`. Every negative-power estimate in `physicalQ`
is therefore automatically an estimate in `(1 - t)^(-·)`, uniformly in the
spatial variable. -/
theorem one_sub_le_physicalQ {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t : ℝ} (ht : t < 1) (y : ESpace) :
    1 - t ≤ physicalQ par (t, y) := by
  have ha : (0 : ℝ) < 2 * par := by linarith
  have ha1 : (2 : ℝ) * par < 1 := by linarith
  have hτ : (0 : ℝ) < 1 - t := by linarith
  obtain ⟨hz, hq⟩ := Navier.Construction.SimilarityCoordinates.coordinateQ_spec
    ha ha1 (p := (1 - t, y 2)) hτ
  have hq' : Navier.Construction.SimilarityCoordinates.forwardScalar (2 * par)
      (y 2) (Navier.Construction.SimilarityCoordinates.coordinateQ
        (2 * par) (1 - t, y 2)) = 1 - t := by simpa using hq
  show 1 - t ≤ Navier.Construction.SimilarityCoordinates.coordinateQ
    (2 * par) (1 - t, y 2)
  -- rewrite only the LHS occurrence of `1 - t` (the pair argument must stay)
  nth_rw 1 [← hq']
  exact forwardScalar_le_self hz.le

/-- On the symmetry axis the similarity coordinate equals the remaining time
exactly: `physicalQ h (t, 0) = 1 - t`. -/
theorem physicalQ_axis {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t : ℝ} (ht : t < 1) : physicalQ par (t, 0) = 1 - t := by
  have ha : (0 : ℝ) < 2 * par := by linarith
  have ha1 : (2 : ℝ) * par < 1 := by linarith
  have hτ : (0 : ℝ) < 1 - t := by linarith
  have hf0 : Navier.Construction.SimilarityCoordinates.forwardScalar
      (2 * par) (0 : ℝ) (1 - t) = 1 - t := by
    show (1 - t) - (0 : ℝ) ^ 2 * (1 - t) ^ (2 * par) = 1 - t
    ring
  have heq : Navier.Construction.SimilarityCoordinates.coordinateQ
      (2 * par) (1 - t, (0 : ℝ)) = 1 - t :=
    ((Navier.Construction.SimilarityCoordinates.eq_coordinateQ ha ha1
      (p := (1 - t, (0 : ℝ))) hτ hτ hf0).symm)
  have hz : (Navier.Construction.AxisymmetricFields.profilePoint t (0 : ESpace)).2.2
      = (0 : ℝ) := by
    show (0 : ESpace) 2 = (0 : ℝ)
    simp
  have h1 : (Navier.Construction.AxisymmetricFields.profilePoint t (0 : ESpace)).1
      = t := rfl
  unfold physicalQ Navier.Construction.SimilarityProfile.q
  rw [h1, hz]
  exact heq

/-! ## 2. The bridge: spatially-uniform `physicalQ` vorticity envelopes. -/

/-- **`q`-envelope → the named scalar leaf.** If the selected-profile
competitor `u` satisfies a spatially-uniform negative-power bound
`officialEuclideanNorm (vorticity (uncurry u) t y) ≤ c₂ · physicalQ par (t, y)^(-α)`
on `[t₀, 1)` (the format in which the stage machinery emits estimates) and a
pointwise axis lower bound of the same power (the format produced by the
exact-axis-vorticity computations, e.g. lane L6b4's `axis_vorticity_origin`
at exponent `A h + 1/2 = 1 + h > 1`), then `VorticityRateBound u` holds via
the sandwich bridge. The upper half converts by `one_sub_le_physicalQ` (the
`q`-uniform bound is strictly stronger than a pointwise-in-`V` `(1-t)`
bound); the lower half converts by `vort_le_V` at the axis point. -/
theorem vorticityRateBound_of_q_curlBound
    {u p f : _} (h : Properties u p f)
    {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (haxis : ∀ t ∈ Ico t₀ (1 : ℝ),
      c₁ * (1 - t) ^ (-α) ≤
        officialEuclideanNorm (vorticity (uncurry u) t (0 : Navier.Space)))
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ y : ESpace,
      officialEuclideanNorm (vorticity (uncurry u) t (y : Navier.Space)) ≤
        c₂ * physicalQ par (t, y) ^ (-α)) :
    VorticityRateBound u := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  refine vorticityRateBound_of_sandwich_for h ht₀ hα hc₁ hc₂ ?_ ?_
  · intro t ht
    exact (haxis t ht).trans
      (vort_le_V h.velocity_smooth hK hsupp ⟨ht₀.1.trans ht.1, ht.2⟩
        (0 : Navier.Space))
  · intro t ht
    show (⨆ x : Navier.Space, officialEuclideanNorm (vorticity (uncurry u) t x)) ≤
      c₂ * (1 - t) ^ (-α)
    refine ciSup_le fun x => ?_
    -- the Euclidean carrier of the Navier.Space point (cf. fromPiCLM/toPiCLM)
    set y : ESpace := WithLp.toLp 2 x
    have hyc : (y : Navier.Space) = x := rfl
    have h1 := hup t ht y
    rw [hyc] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hc₂)
    -- physicalQ par (t, y) ^ (-α) ≤ (1 - t) ^ (-α): antitone in the base at
    -- a negative exponent, via the coordinate comparison.
    refine Real.rpow_le_rpow_of_nonpos (by linarith [ht.2])
      (one_sub_le_physicalQ hpar hpar1 ht.2 y) (by linarith)

/-- The `q`-envelope through the Grönwall pair. -/
theorem gronwall_pair_of_q_curlBound
    {u p f : _} (h : Properties u p f)
    {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (haxis : ∀ t ∈ Ico t₀ (1 : ℝ),
      c₁ * (1 - t) ^ (-α) ≤
        officialEuclideanNorm (vorticity (uncurry u) t (0 : Navier.Space)))
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ y : ESpace,
      officialEuclideanNorm (vorticity (uncurry u) t (y : Navier.Space)) ≤
        c₂ * physicalQ par (t, y) ^ (-α)) :
    GronwallPair u :=
  gronwall_pair_of_rate_bound h
    (vorticityRateBound_of_q_curlBound h hpar hpar1 ht₀ hα hc₁ hc₂ haxis hup)

/-- The `q`-envelope diverges the running vorticity integral. -/
theorem vorticity_integral_divergence_of_q_curlBound
    {u p f : _} (h : Properties u p f)
    {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (haxis : ∀ t ∈ Ico t₀ (1 : ℝ),
      c₁ * (1 - t) ^ (-α) ≤
        officialEuclideanNorm (vorticity (uncurry u) t (0 : Navier.Space)))
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ y : ESpace,
      officialEuclideanNorm (vorticity (uncurry u) t (y : Navier.Space)) ≤
        c₂ * physicalQ par (t, y) ^ (-α)) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B :=
  vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_q_curlBound h hpar hpar1 ht₀ hα hc₁ hc₂ haxis hup)

/-- The `q`-envelope diverges the vorticity `L¹` integral on `[0, 1]`. -/
theorem lintegral_vorticity_integral_divergence_of_q_curlBound
    {u p f : _} (h : Properties u p f)
    {par : ℝ} (hpar : 0 < par) (hpar1 : par < 1 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (haxis : ∀ t ∈ Ico t₀ (1 : ℝ),
      c₁ * (1 - t) ^ (-α) ≤
        officialEuclideanNorm (vorticity (uncurry u) t (0 : Navier.Space)))
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ y : ESpace,
      officialEuclideanNorm (vorticity (uncurry u) t (y : Navier.Space)) ≤
        c₂ * physicalQ par (t, y) ^ (-α)) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ :=
  lintegral_vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_q_curlBound h hpar hpar1 ht₀ hα hc₁ hc₂ haxis hup)

end Navier.Analysis.BKMProfileEnvelope

#check @Navier.Analysis.BKMProfileEnvelope.forwardScalar_le_self
#check @Navier.Analysis.BKMProfileEnvelope.one_sub_le_physicalQ
#check @Navier.Analysis.BKMProfileEnvelope.physicalQ_axis
#check @Navier.Analysis.BKMProfileEnvelope.vorticityRateBound_of_q_curlBound
#check @Navier.Analysis.BKMProfileEnvelope.gronwall_pair_of_q_curlBound
#check @Navier.Analysis.BKMProfileEnvelope.vorticity_integral_divergence_of_q_curlBound
#check @Navier.Analysis.BKMProfileEnvelope.lintegral_vorticity_integral_divergence_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.forwardScalar_le_self
#print axioms Navier.Analysis.BKMProfileEnvelope.one_sub_le_physicalQ
#print axioms Navier.Analysis.BKMProfileEnvelope.physicalQ_axis
#print axioms Navier.Analysis.BKMProfileEnvelope.vorticityRateBound_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.gronwall_pair_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.vorticity_integral_divergence_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.lintegral_vorticity_integral_divergence_of_q_curlBound
