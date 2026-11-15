/-
Lane W10-G26 (2026-09-17): transport 4 of the named T1–T4 residual
(`Analysis/BKMProfileEnvelope.lean`, "Exact surviving proposition (OPEN)"):
the cut + activation sup reduction for the assembled compact candidate.

Frontier wording: "`R3CompactCandidate.velocity` equals the raw sum on
`[3/4, 1)` (`timeSwitch_one_of_three_quarters_le`) and vanishes off
`supportCylinder`, so the spatial sup of the cut field is the sup of the sum
on the cylinder." This module lands that sentence as checked results:

1. `slice_eq_late` — pointwise activation removal: for `3/4 ≤ t`,
   `velocity A B (t, x) = cutVelocity A (t, x) + cutPotential B (t, x)`.
2. `V_velocity_eq_sup_cyl` — the peak-vorticity profile equals the cylinder
   sup of the construction spatial curl of the (time-)slice: the weld
   `BKMEnvAxis.vort_eq_spatialCurl` transports `V` from the official
   coordinates, the `WithLp` bijection transfers the sup to the construction
   carrier (`iSup_toLp_eq`), and `curl_eq_zero_of_not_mem_tsupport` +
   `velocity_supported` kill the complement of the closed cylinder
   (`iSup_space_eq_cyl`). No smoothness of `A`, `B` beyond that of the
   assembled field is used here.
3. `V_velocity_le_cylSums` — the cut potential and direct sums split:
   `V (velocity A B) t` is at most the sum of the two cylinder sups
   `⨆ ‖spatialCurl (cutVelocity A)‖ + ⨆ ‖spatialCurl (cutPotential B)‖`.
   The split consumes pointwise `C^∞` time-slice regularity of the raw sums
   (hypotheses `hAs`, `hBs`).
4. `polyUpper_of_cylSums` and `vorticityRateBound_sel_of_cylSums` — the
   envelope consumer: two power-law bounds (one rate `β`) on the two
   cylinder sups feed `BKMEnvAxis.vorticityRateBound_sel_of_polyUpper`,
   advancing the single named `hup` hypothesis of the selected-field bridge
   to the two named cylinder-sup obligations.
5. Transport 3, the Leibniz decomposition of the two cut curls into raw slice
   sups (`cutVelocity_cylSup_le_rawJets`,
   `cutPotential_cylSup_le_rawJets`, `vorticityRateBound_sel_of_rawJets`):
   added by lane MSW-NAVIER-VRTY-1114 (2026-11-14).  The two cylinder-sup
   obligations `hA`, `hB` are now reducible to one named hypothesis — a raw
   slice-jet envelope of the sums at orders `≤ 2`.

WHAT THIS MODULE DOES NOT PROVE: it does not discharge `VorticityRateBound
(uSel aSel)` — the raw slice-jet envelope supplied to transport 3 is a live
obligation (transport T1's missing low-stage table `hK`), and this module's
crown corollaries are conditional on it. No status prose elsewhere is
superseded by this file.
-/
import Navier.Analysis.BKMEnvAxis

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Analysis.BKMProfileGronwallPair Navier.Analysis.BKMProfileRateBound
open Navier.Analysis.BKMProfileSelectedEnvelope
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Construction ProblemStatement SpatialCurl
open SpatialLocalization
open Navier.Analysis.BKMEnvAxis

namespace Navier.Analysis.BKMEnvCut

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev Cyl := (SpatialLocalization.supportCylinder : Set ESpace)

/-- The official Euclidean norm is the construction-carrier norm: the
`WithLp` transport is the identity on data. -/
theorem officialEuclideanNorm_cast (v : ESpace) :
    officialEuclideanNorm (v : Navier.Space) = ‖v‖ := rfl

/-- The origin lies in the spatial support cylinder. -/
private theorem zero_mem_cyl : (0 : ESpace) ∈ Cyl := by
  simp [Cyl, SpatialLocalization.supportCylinder, SpatialLocalization.radialSquare]

/-- A continuous function vanishing off the closed cylinder has bounded
range. -/
private theorem bddAbove_of_vanishing {g : ESpace → ℝ}
    (hgc : Continuous g) (hg0 : ∀ x ∉ Cyl, g x = 0) : BddAbove (Set.range g) := by
  classical
  have hrange : Set.range g ⊆ g '' Cyl ∪ {0} := by
    intro v hv
    obtain ⟨x, rfl⟩ := hv
    by_cases hx : x ∈ Cyl
    · exact Or.inl ⟨x, hx, rfl⟩
    · rw [hg0 x hx]; exact Or.inr (Set.mem_singleton 0)
  exact BddAbove.mono hrange
    (BddAbove.union (IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder
      hgc.continuousOn) isCompact_singleton.bddAbove)

/-- The full-space sup of a nonnegative function vanishing off the cylinder
equals the cylinder sup. -/
private theorem iSup_space_eq_cyl {g : ESpace → ℝ}
    (hg0 : ∀ x ∉ Cyl, g x = 0) (hgbdd : BddAbove (Set.range g))
    (hgnn : ∀ x, 0 ≤ g x) : (⨆ x : ESpace, g x) = ⨆ x ∈ Cyl, g x := by
  classical
  haveI : Nonempty { x // x ∈ Cyl } := ⟨⟨0, zero_mem_cyl⟩⟩
  have hsub : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) => g a.1)) :=
    BddAbove.mono (Set.range_comp_subset_range (f := (fun (a : { x // x ∈ Cyl }) => (a : ESpace)))
      (g := g)) hgbdd
  have hcvt : (⨆ x ∈ Cyl, g x) = ⨆ (a : { x // x ∈ Cyl }), g a.1 :=
    cbiSup_eq_ciSup_subtype (p := fun x : ESpace => x ∈ Cyl)
      (f := fun (x : ESpace) (_ : x ∈ Cyl) => g x) hsub
      (by rw [Real.sSup_empty]; exact (hgnn 0).trans (le_ciSup hsub ⟨0, zero_mem_cyl⟩))
  refine (le_antisymm ?_ ?_).trans hcvt.symm
  · refine ciSup_le fun y => by
      by_cases hy : y ∈ Cyl
      · exact le_ciSup hsub ⟨y, hy⟩
      · rw [hg0 y hy]
        exact (hgnn 0).trans (le_ciSup hsub ⟨0, zero_mem_cyl⟩)
  · exact ciSup_le fun a => le_ciSup hgbdd a.1

/-- The `WithLp` bijection transfers a bounded sup from the construction
carrier to the official coordinates. -/
private theorem iSup_toLp_eq {g : ESpace → ℝ} (hb : BddAbove (Set.range g)) :
    (⨆ x : Navier.Space, g (WithLp.toLp 2 x)) = ⨆ y : ESpace, g y := by
  refine le_antisymm
    (ciSup_le fun x => le_ciSup hb (WithLp.toLp 2 x))
    (ciSup_le fun y => ?_)
  have hb2 : BddAbove (Set.range (fun x : Navier.Space => g (WithLp.toLp 2 x))) :=
    BddAbove.mono (Set.range_comp_subset_range
      (f := fun (x : Navier.Space) => WithLp.toLp 2 x) (g := g)) hb
  have heq : WithLp.toLp 2 (WithLp.equiv 2 Navier.Space y) = y := by
    rw [← WithLp.equiv_symm_apply]
    exact Equiv.symm_apply_apply _ _
  rw [← heq]
  exact le_ciSup hb2 (WithLp.equiv 2 Navier.Space y)

/-- The iterated cylinder sup converts to a subtype sup once the subtype
function is bounded below-defaulted (`sSup ∅ = 0 ≤ sup`). -/
private theorem cylSup_eq_subtype {h : ESpace → ℝ}
    (hbdd : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) => h a.1)))
    (h0 : 0 ≤ ⨆ (a : { x // x ∈ Cyl }), h a.1) :
    (⨆ x ∈ Cyl, h x) = ⨆ (a : { x // x ∈ Cyl }), h a.1 := by
  refine cbiSup_eq_ciSup_subtype (p := fun x : ESpace => x ∈ Cyl)
    (f := fun (x : ESpace) (_ : x ∈ Cyl) => h x) hbdd ?_
  rw [Real.sSup_empty]
  exact h0

/-- **Activation removal (first half of transport 4).** On `[3/4, 1)` the
time switch is one, so the assembled compact velocity is exactly the sum of
the two cut fields. -/
theorem slice_eq_late {A B : ProblemStatement.VelocityField} {t : ℝ} (ht : (3 / 4 : ℝ) ≤ t) (x : ESpace) :
    R3CompactCandidate.velocity A B (t, x) =
      SpatialLocalization.cutVelocity A (t, x) + SpatialLocalization.cutPotential B (t, x) := by
  change TimeLocalization.activatedVelocity
      (fun z => SpatialLocalization.cutVelocity A z + SpatialLocalization.cutPotential B z)
      (t, x) = _
  rw [TimeLocalization.activatedVelocity_eq_late
      (fun z => SpatialLocalization.cutVelocity A z + SpatialLocalization.cutPotential B z) ht x]

/-- The closed cylinder bounds the spatial slice support of the assembled
velocity at every time. -/
theorem slice_tsupport_subset {A B : ProblemStatement.VelocityField} (t : ℝ) :
    tsupport (fun x : ESpace => R3CompactCandidate.velocity A B (t, x)) ⊆ Cyl :=
  closure_minimal (fun x hx => by
    by_contra hn
    exact (Function.mem_support.mp hx)
      (R3CompactCandidate.velocity_supported A B t x hn))
    SpatialLocalization.isClosed_supportCylinder

/-- **Transport 4, sup reduction.** For late `t`, the peak-vorticity profile
of the assembled compact velocity is exactly the supremum of the construction
spatial curl of its time-slice over the closed cylinder. -/
theorem V_velocity_eq_sup_cyl {A B : ProblemStatement.VelocityField}
    (hvw : ContDiffOn ℝ ∞ (R3CompactCandidate.velocity A B) preSingularDomain)
    {t : ℝ} (ht : t ∈ Ico (3 / 4 : ℝ) (1 : ℝ)) :
    V (R3CompactCandidate.velocity A B) t =
      ⨆ x ∈ Cyl, ‖spatialCurl (R3CompactCandidate.velocity A B) (t, x)‖ := by
  classical
  set w := R3CompactCandidate.velocity A B with hwdef
  have ht0 : t ∈ Ico (0 : ℝ) 1 := ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans ht.1, ht.2⟩
  have hvw' : ContDiffOn ℝ ∞ w (Ico (0 : ℝ) 1 ×ˢ (univ : Set ESpace)) := hvw
  have hsl : ContDiff ℝ ∞ (fun x : ESpace => w (t, x)) := contDiff_spatialSlice hvw' ht0
  have hc : Continuous (fun y : ESpace => ‖spatialCurl w (t, y)‖) :=
    continuous_norm.comp ((contDiff_curl (m := (1 : WithTop ℕ∞)) hsl (by simp)).continuous)
  have hg0 : ∀ y : ESpace, y ∉ Cyl → spatialCurl w (t, y) = 0 := fun y hy =>
    curl_eq_zero_of_not_mem_tsupport (fun hts => hy (slice_tsupport_subset (A := A) (B := B) t hts))
  have hgbdd : BddAbove (Set.range (fun y : ESpace => ‖spatialCurl w (t, y)‖)) :=
    bddAbove_of_vanishing hc (fun y hy => by rw [norm_eq_zero, hg0 y hy])
  calc V w t
      _ = ⨆ x : Navier.Space, ‖spatialCurl w (t, WithLp.toLp 2 x)‖ := by
        show (⨆ x : Navier.Space, officialEuclideanNorm (vorticity (uncurry w) t x)) = _
        refine congrArg iSup (funext fun x => ?_)
        rw [vort_eq_spatialCurl hvw ht0 x]
        exact officialEuclideanNorm_cast _
      _ = ⨆ y : ESpace, ‖spatialCurl w (t, y)‖ :=
        iSup_toLp_eq (g := fun y : ESpace => ‖spatialCurl w (t, y)‖) hgbdd
      _ = ⨆ x ∈ Cyl, ‖spatialCurl w (t, x)‖ :=
        iSup_space_eq_cyl (g := fun y : ESpace => ‖spatialCurl w (t, y)‖)
          (fun y hy => by rw [norm_eq_zero, hg0 y hy]) hgbdd (fun y => norm_nonneg _)

/-- The spatial curl of a pointwise sum of twice-differentiable slices. -/
private theorem slice_curl_add {w₁ w₂ : ESpace → ESpace} {y : ESpace}
    (h₁ : ContDiffAt ℝ 2 w₁ y) (h₂ : ContDiffAt ℝ 2 w₂ y) :
    curl (fun z => w₁ z + w₂ z) y = curl w₁ y + curl w₂ y := by
  unfold curl
  show curlLinear (fderiv ℝ (w₁ + w₂) y) = curlLinear (fderiv ℝ w₁ y) + curlLinear (fderiv ℝ w₂ y)
  rw [fderiv_add (h₁.differentiableAt (by simp)) (h₂.differentiableAt (by simp)), map_add]

/-- **Transport 4, pointwise cut split.** With `C^∞` time slices of the raw
sums, the slice curl of the assembled velocity splits into the slice curls of
the cut potential and of the cut direct sum. -/
theorem spatialCurl_velocity_eq {A B : ProblemStatement.VelocityField} {t : ℝ} (ht : (3 / 4 : ℝ) ≤ t)
    (hAs : ContDiffOn ℝ ∞ (fun x : ESpace => A (t, x)) univ)
    (hBs : ContDiffOn ℝ ∞ (fun x : ESpace => B (t, x)) univ) (y : ESpace) :
    spatialCurl (R3CompactCandidate.velocity A B) (t, y) =
      spatialCurl (SpatialLocalization.cutVelocity A) (t, y) +
        spatialCurl (SpatialLocalization.cutPotential B) (t, y) := by
  have hAy : ContDiffAt ℝ ∞ (fun z : ESpace => A (t, z)) y :=
    by simpa [contDiffWithinAt_univ] using hAs y (mem_univ y)
  have hBy : ContDiffAt ℝ ∞ (fun z : ESpace => B (t, z)) y :=
    by simpa [contDiffWithinAt_univ] using hBs y (mem_univ y)
  have hχ : ContDiffAt ℝ ∞ spatialCutoff y := spatialCutoff_contDiff.contDiffAt
  have hAw : ContDiffAt ℝ ∞ (fun z : ESpace => spatialCutoff z • A (t, z)) y :=
    hχ.smul hAy
  have hBw : ContDiffAt ℝ ∞ (fun z : ESpace => spatialCutoff z • B (t, z)) y :=
    hχ.smul hBy
  have h₁ : ContDiffAt ℝ 2 (fun z : ESpace => SpatialLocalization.cutVelocity A (t, z)) y := by
    have hslice : (fun z : ESpace => SpatialLocalization.cutVelocity A (t, z))
        = fun (z : ESpace) => curl (fun w : ESpace => spatialCutoff w • A (t, w)) z := rfl
    rw [hslice]
    exact contDiffAt_curl hAw (by simp)
  have h₂ : ContDiffAt ℝ 2 (fun z : ESpace => SpatialLocalization.cutPotential B (t, z)) y :=
    ContDiffAt.of_le hBw (by simp)
  have hsl : (fun z : ESpace => R3CompactCandidate.velocity A B (t, z))
      = fun z => SpatialLocalization.cutVelocity A (t, z) +
          SpatialLocalization.cutPotential B (t, z) :=
    funext fun z => slice_eq_late ht z
  have key := slice_curl_add (w₁ := fun z : ESpace => SpatialLocalization.cutVelocity A (t, z))
    (w₂ := fun z : ESpace => SpatialLocalization.cutPotential B (t, z)) h₁ h₂
  show curl (fun z : ESpace => R3CompactCandidate.velocity A B (t, z)) y = _
  rw [hsl]
  exact key

/-- **Transport 4, cut + activation sup reduction.** The peak-vorticity
profile of the assembled compact velocity is at most the sum of the two
cylinder sups of the cut fields' slice curls. This is the exact remaining
form of the frontier sentence "the spatial sup of the cut field is the sup of
the sum on the cylinder"; splitting those two sups into RAW stage sups is
transport 3. -/
theorem V_velocity_le_cylSums {A B : ProblemStatement.VelocityField}
    (hvw : ContDiffOn ℝ ∞ (R3CompactCandidate.velocity A B) preSingularDomain)
    {t : ℝ} (ht : t ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hAs : ContDiffOn ℝ ∞ (fun x : ESpace => A (t, x)) univ)
    (hBs : ContDiffOn ℝ ∞ (fun x : ESpace => B (t, x)) univ) :
    V (R3CompactCandidate.velocity A B) t ≤
      (⨆ x ∈ Cyl, ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖) +
        (⨆ x ∈ Cyl, ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖) := by
  classical
  haveI : Nonempty { x // x ∈ Cyl } := ⟨⟨0, zero_mem_cyl⟩⟩
  -- Function-level `C^∞` regularity of the two cut-field potential slices.
  have hψA : ContDiff ℝ ∞ (fun z : ESpace => spatialCutoff z • A (t, z)) :=
    spatialCutoff_contDiff.smul (contDiffOn_univ.mp hAs)
  have hψB : ContDiff ℝ ∞ (fun z : ESpace => spatialCutoff z • B (t, z)) :=
    spatialCutoff_contDiff.smul (contDiffOn_univ.mp hBs)
  have hslA : (fun y : ESpace => SpatialLocalization.cutVelocity A (t, y))
      = fun (y : ESpace) => curl (fun w : ESpace => spatialCutoff w • A (t, w)) y := rfl
  have hc2 : ContDiff ℝ 2 (fun y : ESpace => SpatialLocalization.cutVelocity A (t, y)) := by
    rw [hslA]; exact contDiff_curl (m := (2 : WithTop ℕ∞)) hψA (by simp)
  have hcA : Continuous (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutVelocity A)
      (t, x)‖) :=
    continuous_norm.comp ((contDiff_curl (m := (1 : WithTop ℕ∞)) hc2 (by norm_num)).continuous)
  have hBsl : ContDiff ℝ ∞ (fun y : ESpace => SpatialLocalization.cutPotential B (t, y)) := hψB
  have hcB : Continuous (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutPotential B)
      (t, x)‖) :=
    continuous_norm.comp ((contDiff_curl (m := (1 : WithTop ℕ∞)) hBsl (by simp)).continuous)
  have hB1 : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) =>
      ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, a.1)‖)) := by
    have hrange : Set.range (fun (a : { x // x ∈ Cyl }) =>
        ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, a.1)‖)
        = (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖) '' Cyl := by
      ext v; simp
    rw [hrange]
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hcA.continuousOn
  have hB2 : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) =>
      ‖spatialCurl (SpatialLocalization.cutPotential B) (t, a.1)‖)) := by
    have hrange : Set.range (fun (a : { x // x ∈ Cyl }) =>
        ‖spatialCurl (SpatialLocalization.cutPotential B) (t, a.1)‖)
        = (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖) '' Cyl := by
      ext v; simp
    rw [hrange]
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hcB.continuousOn
  have hB0 : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) =>
      ‖spatialCurl (R3CompactCandidate.velocity A B) (t, a.1)‖)) := by
    have hrange : Set.range (fun (a : { x // x ∈ Cyl }) =>
        ‖spatialCurl (R3CompactCandidate.velocity A B) (t, a.1)‖)
        = (fun x : ESpace => ‖spatialCurl (R3CompactCandidate.velocity A B) (t, x)‖) '' Cyl := by
      ext v; simp
    rw [hrange]
    have ht0 : t ∈ Ico (0 : ℝ) (1 : ℝ) := ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans ht.1, ht.2⟩
    have hvw' : ContDiffOn ℝ ∞ (R3CompactCandidate.velocity A B)
        (Ico (0 : ℝ) 1 ×ˢ (univ : Set ESpace)) := hvw
    have hslw : ContDiff ℝ ∞ (fun x : ESpace => R3CompactCandidate.velocity A B (t, x)) :=
      contDiff_spatialSlice hvw' ht0
    have hcw : Continuous (fun y : ESpace =>
        ‖spatialCurl (R3CompactCandidate.velocity A B) (t, y)‖) :=
      continuous_norm.comp
        ((contDiff_curl (m := (1 : WithTop ℕ∞)) hslw (by simp)).continuous)
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hcw.continuousOn
  rw [V_velocity_eq_sup_cyl hvw ht]
  rw [cylSup_eq_subtype (h := fun y : ESpace =>
        ‖spatialCurl (R3CompactCandidate.velocity A B) (t, y)‖) hB0
      ((norm_nonneg _).trans (le_ciSup hB0 ⟨0, zero_mem_cyl⟩)),
    cylSup_eq_subtype (h := fun y : ESpace =>
        ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, y)‖) hB1
      ((norm_nonneg _).trans (le_ciSup hB1 ⟨0, zero_mem_cyl⟩)),
    cylSup_eq_subtype (h := fun y : ESpace =>
        ‖spatialCurl (SpatialLocalization.cutPotential B) (t, y)‖) hB2
      ((norm_nonneg _).trans (le_ciSup hB2 ⟨0, zero_mem_cyl⟩))]
  refine ciSup_le fun a => ?_
  rw [spatialCurl_velocity_eq ht.1 hAs hBs (a : ESpace)]
  exact (norm_add_le _ _).trans (add_le_add (le_ciSup hB1 a) (le_ciSup hB2 a))

/-- **Envelope packaging.** Two power-law bounds (one rate `β`) on the two
cylinder sups of the cut fields give the polynomial upper envelope of `V`
for the assembled compact velocity — the exact shape consumed by
`BKMEnvAxis.vorticityRateBound_sel_of_polyUpper`. -/
theorem polyUpper_of_cylSums {A B : ProblemStatement.VelocityField}
    (hvw : ContDiffOn ℝ ∞ (R3CompactCandidate.velocity A B) preSingularDomain)
    {β : ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hAs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞ (fun x : ESpace => A (t, x)) univ)
    (hBs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞ (fun x : ESpace => B (t, x)) univ)
    (hA : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ Cyl,
        ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖ ≤ c₁ * (1 - t) ^ (-β))
    (hB : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ Cyl,
        ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖ ≤ c₂ * (1 - t) ^ (-β)) :
    ∀ t ∈ Ico t₀ (1 : ℝ),
      V (R3CompactCandidate.velocity A B) t ≤ (c₁ + c₂) * (1 - t) ^ (-β) := by
  intro t ht
  exact (V_velocity_le_cylSums hvw ⟨le_trans ht₀.1 ht.1, ht.2⟩ (hAs t ht) (hBs t ht)).trans
    (by rw [add_mul]; exact add_le_add (hA t ht) (hB t ht))

/-- **Crown feeder.** With the assembled selected field's own smoothness and
the two cylinder-sup power-law bounds, the selected-field rate bound follows
from `BKMEnvAxis.vorticityRateBound_sel_of_polyUpper`. The remaining live
obligations for the unconditional crown are now the two named cylinder-sup
hypotheses `hA`, `hB` (transports T1–T3), not the single merged `hup`. -/
theorem vorticityRateBound_sel_of_cylSums
    {β : ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hv : ContDiffOn ℝ ∞ (uSel aSel) preSingularDomain)
    (hAs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞
      (fun x : ESpace => ASum aSel (t, x)) univ)
    (hBs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞
      (fun x : ESpace => BSum aSel (t, x)) univ)
    (hA : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ Cyl,
        ‖spatialCurl (SpatialLocalization.cutVelocity (ASum aSel)) (t, x)‖ ≤ c₁ * (1 - t) ^ (-β))
    (hB : ∀ t ∈ Ico t₀ (1 : ℝ), ⨆ x ∈ Cyl,
        ‖spatialCurl (SpatialLocalization.cutPotential (BSum aSel)) (t, x)‖ ≤ c₂ * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aSel) :=
  vorticityRateBound_sel_of_polyUpper (add_nonneg hc₁ hc₂)
    ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans ht₀.1, ht₀.2⟩
    (polyUpper_of_cylSums hv hc₁ hc₂ ht₀ hAs hBs hA hB)

/-! ### Transport T3: the cutoff Leibniz bridge

The two named cylinder-sup hypotheses of `polyUpper_of_cylSums` are suprema of
*cut* curls.  This section lands transport 3, the reduction announced in item 3
of the module header: those suprema follow from cylinder suprema of the **raw**
spatial-slice derivatives of the sums themselves, at the same rate `β`, with a
multiplicative constant built only from the spatial cutoff and the fixed curl
operator.

The mechanism has two parts.  `slice_smul_jet_le` is the binomial Leibniz rule
`norm_iteratedFDeriv_smul_le` read on the spatial slice, where the multiplier
`SpatialLocalization.spatialCutoff` is a function of space alone (no spacetime
composition is needed).  `curl_norm_le` and `curl_curl_norm_le` price the curl
through `SpatialCurl.fderiv_curl`: one spatial derivative plus the fixed
operator norm `‖curlLinear‖`.

Satisfiability.  The hypotheses are not vacuous: a spatially constant raw slice
has every derivative of order `≥ 1` equal to zero, so `hjet` holds with `β = 0`
and `c = ⨆ x ∈ Cyl, ‖A (t, x)‖`.  What the repository does not supply is the
raw slice-jet envelope for the actual sums: that is the missing low-stage table
`hK` of transport T1, whose output format
`CS_PotentialSumEnvelope.potentialSum_negPower_envelope_physical` emits at the
spacetime level, and which this bridge is written to consume. -/

/-- The sum of the cylinder suprema of the spatial cutoff's iterated
derivatives of orders `0`, `1` and `2`. -/
noncomputable def cutJetBound : ℝ :=
  ∑ i ∈ Finset.range 3, ⨆ x ∈ Cyl, ‖iteratedFDeriv ℝ i SpatialLocalization.spatialCutoff x‖

/-- A continuous nonnegative function is bounded at a cylinder point by its
cylinder sup: compactness of the cylinder supplies the boundedness that
`le_ciSup` demands. -/
private theorem cylLe_ciSup {g : ESpace → ℝ} (hg : Continuous g) (hgnn : ∀ y, 0 ≤ g y)
    {x : ESpace} (hx : x ∈ Cyl) : g x ≤ ⨆ y ∈ Cyl, g y := by
  classical
  haveI : Nonempty { y // y ∈ Cyl } := ⟨⟨0, zero_mem_cyl⟩⟩
  have hrange : Set.range (fun (a : { y // y ∈ Cyl }) => g (a : ESpace)) = g '' Cyl := by
    ext v; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  have hbdd : BddAbove (Set.range (fun (a : { y // y ∈ Cyl }) => g (a : ESpace))) := by
    rw [hrange]
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hg.continuousOn
  have h0 : 0 ≤ ⨆ (a : { y // y ∈ Cyl }), g (a : ESpace) :=
    (hgnn 0).trans (le_ciSup hbdd ⟨0, zero_mem_cyl⟩)
  rw [cylSup_eq_subtype (h := g) hbdd h0]
  exact le_ciSup hbdd ⟨x, hx⟩

/-- The iterated derivatives of a `C^∞` map into a normed space are continuous. -/
private theorem contJet_continuous {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ESpace → V} (hF : ContDiff ℝ ∞ F) (i : ℕ) :
    Continuous (fun x : ESpace => ‖iteratedFDeriv ℝ i F x‖) :=
  continuous_norm.comp (ContDiff.continuous_iteratedFDeriv (by simp) hF)

/-- Every cutoff derivative of order at most two is bounded on the cylinder by
`cutJetBound`. -/
private theorem le_cutJetBound {i : ℕ} (hi : i ≤ 2) {x : ESpace} (hx : x ∈ Cyl) :
    ‖iteratedFDeriv ℝ i SpatialLocalization.spatialCutoff x‖ ≤ cutJetBound := by
  classical
  have hsum : (⨆ y ∈ Cyl, ‖iteratedFDeriv ℝ i SpatialLocalization.spatialCutoff y‖) ≤ cutJetBound :=
    Finset.single_le_sum (f := fun j =>
      ⨆ y ∈ Cyl, ‖iteratedFDeriv ℝ j SpatialLocalization.spatialCutoff y‖)
      (fun j _ => (norm_nonneg _).trans
        (cylLe_ciSup (contJet_continuous SpatialLocalization.spatialCutoff_contDiff j)
          (fun _ => norm_nonneg _) zero_mem_cyl))
      (Finset.mem_range.mpr (by omega : i < 3))
  exact ((cylLe_ciSup (contJet_continuous SpatialLocalization.spatialCutoff_contDiff i)
    (fun _ => norm_nonneg _) hx)).trans hsum

/-- The cutoff jet bound is nonnegative: it is a sum of suprema of norms. -/
theorem cutJetBound_nonneg : 0 ≤ cutJetBound :=
  Finset.sum_nonneg fun j _ => (norm_nonneg _).trans
    (cylLe_ciSup (contJet_continuous SpatialLocalization.spatialCutoff_contDiff j)
      (fun _ => norm_nonneg _) zero_mem_cyl)

/-- **Leibniz bridge on the slice.** Cutting a `C^∞` spatial slice by the
spatial cutoff costs, at order `m ≤ 2` and on the cylinder, at most `2^m` times
the cutoff's derivative bound `cutJetBound` times the cylinder sup of the raw
slice derivatives up to order `m`. -/
private theorem slice_smul_jet_le {F : ESpace → ESpace} (hF : ContDiff ℝ ∞ F) {m : ℕ} (hm : m ≤ 2)
    {x : ESpace} (hx : x ∈ Cyl) {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : ∀ k ≤ m, ⨆ y ∈ Cyl, ‖iteratedFDeriv ℝ k F y‖ ≤ J) :
    ‖iteratedFDeriv ℝ m (fun y : ESpace => SpatialLocalization.spatialCutoff y • F y) x‖ ≤
      (2 : ℝ) ^ m * cutJetBound * J := by
  classical
  have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = (2 : ℝ) ^ m := by
    norm_cast
    exact Nat.sum_range_choose m
  have hcb := cutJetBound_nonneg
  calc ‖iteratedFDeriv ℝ m (fun y : ESpace => SpatialLocalization.spatialCutoff y • F y) x‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i SpatialLocalization.spatialCutoff x‖ *
            ‖iteratedFDeriv ℝ (m - i) F x‖ :=
        norm_iteratedFDeriv_smul_le SpatialLocalization.spatialCutoff_contDiff hF x (by simp)
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * cutJetBound * J := by
        refine Finset.sum_le_sum fun i hi => ?_
        have him : i ≤ m := by
          rw [Finset.mem_range] at hi
          omega
        have hFle : ‖iteratedFDeriv ℝ (m - i) F x‖ ≤ J :=
          (cylLe_ciSup (contJet_continuous hF (m - i)) (fun _ => norm_nonneg _) hx).trans
            (hJ (m - i) (by omega))
        calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i SpatialLocalization.spatialCutoff x‖ *
              ‖iteratedFDeriv ℝ (m - i) F x‖
            ≤ (m.choose i : ℝ) * cutJetBound * ‖iteratedFDeriv ℝ (m - i) F x‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_cutJetBound (by omega) hx) (Nat.cast_nonneg _))
                (norm_nonneg _)
          _ ≤ (m.choose i : ℝ) * cutJetBound * J :=
              mul_le_mul_of_nonneg_left hFle
                (mul_nonneg (Nat.cast_nonneg _) hcb)
      _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * cutJetBound * J := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = (2 : ℝ) ^ m * cutJetBound * J := by rw [hsum]

/-- The order-one jet is the Fréchet derivative. -/
private theorem norm_jet1_eq_fderiv {F : ESpace → ESpace} {x : ESpace} :
    ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]

/-- The order-two jet is the derivative of the derivative. -/
private theorem norm_jet2_eq_fderiv_fderiv {F : ESpace → ESpace} {x : ESpace} :
    ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
    norm_iteratedFDeriv_zero]

/-- **Curl cost, one derivative.** -/
private theorem curl_norm_le {F : ESpace → ESpace} {x : ESpace} (hF : ContDiffAt ℝ 2 F x) :
    ‖curl F x‖ ≤ ‖curlLinear‖ * ‖iteratedFDeriv ℝ 1 F x‖ :=
  calc ‖curl F x‖ = ‖curlLinear (fderiv ℝ F x)‖ := rfl
    _ ≤ ‖curlLinear‖ * ‖fderiv ℝ F x‖ := curlLinear.le_opNorm _
    _ = ‖curlLinear‖ * ‖iteratedFDeriv ℝ 1 F x‖ := by rw [← norm_jet1_eq_fderiv]

/-- The operator norm of a composition is at most the product of the operator
norms, proved from the definition of the operator norm. -/
private theorem curlLinear_comp_norm_le (T : ESpace →L[ℝ] (ESpace →L[ℝ] ESpace)) :
    ‖curlLinear.comp T‖ ≤ ‖curlLinear‖ * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (M := ‖curlLinear‖ * ‖T‖) (by positivity) ?_
  intro v
  calc ‖(curlLinear.comp T) v‖ = ‖curlLinear (T v)‖ := rfl
    _ ≤ ‖curlLinear‖ * ‖T v‖ := curlLinear.le_opNorm _
    _ ≤ ‖curlLinear‖ * (‖T‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm v) (by positivity)
    _ ≤ (‖curlLinear‖ * ‖T‖) * ‖v‖ := by rw [mul_assoc]

/-- **Curl cost, two derivatives.** Taking the curl twice costs two spatial
derivatives and the square of the fixed curl-operator norm. -/
private theorem curl_curl_norm_le {F : ESpace → ESpace} {x : ESpace}
    (hF : ContDiffAt ℝ 2 F x) :
    ‖curl (curl F) x‖ ≤ ‖curlLinear‖ ^ 2 * ‖iteratedFDeriv ℝ 2 F x‖ :=
  calc ‖curl (curl F) x‖ = ‖curlLinear (fderiv ℝ (curl F) x)‖ := rfl
    _ = ‖curlLinear (curlLinear.comp (fderiv ℝ (fderiv ℝ F) x))‖ := by rw [fderiv_curl hF]
    _ ≤ ‖curlLinear‖ * ‖curlLinear.comp (fderiv ℝ (fderiv ℝ F) x)‖ := curlLinear.le_opNorm _
    _ ≤ ‖curlLinear‖ * (‖curlLinear‖ * ‖fderiv ℝ (fderiv ℝ F) x‖) :=
        mul_le_mul_of_nonneg_left (curlLinear_comp_norm_le _) (by positivity)
    _ = ‖curlLinear‖ ^ 2 * ‖iteratedFDeriv ℝ 2 F x‖ := by
        rw [← norm_jet2_eq_fderiv_fderiv, pow_two]
        ring

/-- **Transport T3, `hA` side.** A raw slice-jet envelope for `A` at rate `β`
gives the cylinder-sup bound on the curl of the cut direct sum
`SpatialLocalization.cutVelocity A`, with constant
`4 · ‖curlLinear‖² · cutJetBound · c`. -/
theorem cutVelocity_cylSup_le_rawJets {A : ProblemStatement.VelocityField} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (1 : ℝ))
    (hAs : ContDiffOn ℝ ∞ (fun x : ESpace => A (t, x)) univ)
    {c β : ℝ} (hc : 0 ≤ c)
    (hjet : ∀ k ≤ 2, ⨆ x ∈ Cyl,
        ‖iteratedFDeriv ℝ k (fun x : ESpace => A (t, x)) x‖ ≤ c * (1 - t) ^ (-β)) :
    ⨆ x ∈ Cyl, ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖ ≤
      (4 : ℝ) * ‖curlLinear‖ ^ 2 * cutJetBound * c * (1 - t) ^ (-β) := by
  classical
  haveI : Nonempty { x // x ∈ Cyl } := ⟨⟨0, zero_mem_cyl⟩⟩
  have hJ0 : 0 ≤ c * (1 - t) ^ (-β) :=
    mul_nonneg hc (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _)
  have h4 : ((2 : ℝ) ^ 2 : ℝ) = (4 : ℝ) := by norm_num
  have hψ : ContDiff ℝ ∞ (fun z : ESpace => SpatialLocalization.spatialCutoff z • A (t, z)) :=
    SpatialLocalization.spatialCutoff_contDiff.smul (contDiffOn_univ.mp hAs)
  have hsl : (fun y : ESpace => SpatialLocalization.cutVelocity A (t, y)) =
      fun y : ESpace => curl (fun z : ESpace => SpatialLocalization.spatialCutoff z • A (t, z)) y :=
    rfl
  have hc2 : ContDiff ℝ 2 (fun y : ESpace => SpatialLocalization.cutVelocity A (t, y)) := by
    rw [hsl]; exact contDiff_curl (m := (2 : WithTop ℕ∞)) hψ (by simp)
  have hcont : Continuous (fun x : ESpace =>
      ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖) :=
    continuous_norm.comp
      ((contDiff_curl (m := (1 : WithTop ℕ∞)) hc2 (by norm_num)).continuous)
  have hBdd : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) =>
      ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, (a : ESpace))‖)) := by
    have hrange : Set.range (fun (a : { x // x ∈ Cyl }) =>
        ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, (a : ESpace))‖)
        = (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, x)‖) '' Cyl := by
      ext v; simp
    rw [hrange]
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hcont.continuousOn
  -- The pointwise form of the claim, on the cylinder.
  have hpt : ∀ y : ESpace, y ∈ Cyl →
      ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, y)‖ ≤
        (4 : ℝ) * ‖curlLinear‖ ^ 2 * cutJetBound * c * (1 - t) ^ (-β) := by
    intro y hy
    have hy2 : ContDiffAt ℝ 2
        (fun z : ESpace => SpatialLocalization.spatialCutoff z • A (t, z)) y :=
      ContDiffAt.of_le hψ.contDiffAt (by simp)
    calc ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, y)‖
        = ‖curl (fun w : ESpace => SpatialLocalization.cutVelocity A (t, w)) y‖ := rfl
      _ = ‖curl (curl (fun z : ESpace => SpatialLocalization.spatialCutoff z • A (t, z))) y‖ :=
          by rw [hsl]
      _ ≤ ‖curlLinear‖ ^ 2 * ‖iteratedFDeriv ℝ 2
            (fun z : ESpace => SpatialLocalization.spatialCutoff z • A (t, z)) y‖ :=
          curl_curl_norm_le hy2
      _ ≤ ‖curlLinear‖ ^ 2 * ((2 : ℝ) ^ 2 * cutJetBound * (c * (1 - t) ^ (-β))) :=
          mul_le_mul_of_nonneg_left
            (slice_smul_jet_le (F := fun z : ESpace => A (t, z)) (contDiffOn_univ.mp hAs) (m := 2)
              (by norm_num) hy hJ0 (fun k hk => hjet k (by omega))) (by positivity)
      _ = (4 : ℝ) * ‖curlLinear‖ ^ 2 * cutJetBound * c * (1 - t) ^ (-β) := by
          rw [h4]
          ring
  rw [cylSup_eq_subtype (h := fun y : ESpace =>
        ‖spatialCurl (SpatialLocalization.cutVelocity A) (t, y)‖) hBdd
      ((norm_nonneg _).trans (le_ciSup hBdd ⟨0, zero_mem_cyl⟩))]
  refine ciSup_le fun a => hpt (a : ESpace) a.2

/-- **Transport T3, `hB` side.** The same envelope for `B` gives the
cylinder-sup bound on the curl of the cut potential sum, with constant
`2 · ‖curlLinear‖ · cutJetBound · c`. -/
theorem cutPotential_cylSup_le_rawJets {B : ProblemStatement.VelocityField} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (1 : ℝ))
    (hBs : ContDiffOn ℝ ∞ (fun x : ESpace => B (t, x)) univ)
    {c β : ℝ} (hc : 0 ≤ c)
    (hjet : ∀ k ≤ 2, ⨆ x ∈ Cyl,
        ‖iteratedFDeriv ℝ k (fun x : ESpace => B (t, x)) x‖ ≤ c * (1 - t) ^ (-β)) :
    ⨆ x ∈ Cyl, ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖ ≤
      (2 : ℝ) * ‖curlLinear‖ * cutJetBound * c * (1 - t) ^ (-β) := by
  classical
  haveI : Nonempty { x // x ∈ Cyl } := ⟨⟨0, zero_mem_cyl⟩⟩
  have hJ0 : 0 ≤ c * (1 - t) ^ (-β) :=
    mul_nonneg hc (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _)
  have h2 : ((2 : ℝ) ^ 1 : ℝ) = (2 : ℝ) := by norm_num
  have hψ : ContDiff ℝ ∞ (fun z : ESpace => SpatialLocalization.spatialCutoff z • B (t, z)) :=
    SpatialLocalization.spatialCutoff_contDiff.smul (contDiffOn_univ.mp hBs)
  have hBsl : ContDiff ℝ ∞ (fun y : ESpace => SpatialLocalization.cutPotential B (t, y)) := hψ
  have hsl : (fun y : ESpace => SpatialLocalization.cutPotential B (t, y)) =
      fun y : ESpace => SpatialLocalization.spatialCutoff y • B (t, y) := rfl
  have hcont : Continuous (fun x : ESpace =>
      ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖) :=
    continuous_norm.comp
      ((contDiff_curl (m := (1 : WithTop ℕ∞)) hBsl (by simp)).continuous)
  have hBdd : BddAbove (Set.range (fun (a : { x // x ∈ Cyl }) =>
      ‖spatialCurl (SpatialLocalization.cutPotential B) (t, (a : ESpace))‖)) := by
    have hrange : Set.range (fun (a : { x // x ∈ Cyl }) =>
        ‖spatialCurl (SpatialLocalization.cutPotential B) (t, (a : ESpace))‖)
        = (fun x : ESpace => ‖spatialCurl (SpatialLocalization.cutPotential B) (t, x)‖) '' Cyl := by
      ext v; simp
    rw [hrange]
    exact IsCompact.bddAbove_image SpatialLocalization.isCompact_supportCylinder hcont.continuousOn
  have hpt : ∀ y : ESpace, y ∈ Cyl →
      ‖spatialCurl (SpatialLocalization.cutPotential B) (t, y)‖ ≤
        (2 : ℝ) * ‖curlLinear‖ * cutJetBound * c * (1 - t) ^ (-β) := by
    intro y hy
    have hy2 : ContDiffAt ℝ 2
        (fun z : ESpace => SpatialLocalization.spatialCutoff z • B (t, z)) y :=
      ContDiffAt.of_le hψ.contDiffAt (by simp)
    calc ‖spatialCurl (SpatialLocalization.cutPotential B) (t, y)‖
        = ‖curl (fun w : ESpace => SpatialLocalization.cutPotential B (t, w)) y‖ := rfl
      _ = ‖curl (fun w : ESpace => SpatialLocalization.spatialCutoff w • B (t, w)) y‖ :=
          by rw [hsl]
      _ ≤ ‖curlLinear‖ * ‖iteratedFDeriv ℝ 1
            (fun w : ESpace => SpatialLocalization.spatialCutoff w • B (t, w)) y‖ :=
          curl_norm_le hy2
      _ ≤ ‖curlLinear‖ * ((2 : ℝ) ^ 1 * cutJetBound * (c * (1 - t) ^ (-β))) :=
          mul_le_mul_of_nonneg_left
            (slice_smul_jet_le (F := fun z : ESpace => B (t, z)) (contDiffOn_univ.mp hBs) (m := 1)
              (by norm_num) hy hJ0 (fun k hk => hjet k (by omega))) (by positivity)
      _ = (2 : ℝ) * ‖curlLinear‖ * cutJetBound * c * (1 - t) ^ (-β) := by
          rw [h2]
          ring
  rw [cylSup_eq_subtype (h := fun y : ESpace =>
        ‖spatialCurl (SpatialLocalization.cutPotential B) (t, y)‖) hBdd
      ((norm_nonneg _).trans (le_ciSup hBdd ⟨0, zero_mem_cyl⟩))]
  refine ciSup_le fun a => hpt (a : ESpace) a.2

/-- **Crown feeder at the raw-jet level.** With the assembled selected field's
smoothness and a raw slice-jet envelope for the two sums on `Ico t₀ 1`, the
selected-field rate bound follows.  The live obligation is now a single named
noun: the raw slice-jet envelope itself (transport T1's low-stage table `hK`),
not the two cylinder-sup curl bounds. -/
theorem vorticityRateBound_sel_of_rawJets
    {β c : ℝ} (hc : 0 ≤ c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (3 / 4 : ℝ) (1 : ℝ))
    (hv : ContDiffOn ℝ ∞ (uSel aSel) preSingularDomain)
    (hAs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞
      (fun x : ESpace => ASum aSel (t, x)) univ)
    (hBs : ∀ t ∈ Ico t₀ (1 : ℝ), ContDiffOn ℝ ∞
      (fun x : ESpace => BSum aSel (t, x)) univ)
    (hjetA : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ⨆ x ∈ Cyl,
        ‖iteratedFDeriv ℝ k (fun x : ESpace => ASum aSel (t, x)) x‖ ≤ c * (1 - t) ^ (-β))
    (hjetB : ∀ t ∈ Ico t₀ (1 : ℝ), ∀ k ≤ 2, ⨆ x ∈ Cyl,
        ‖iteratedFDeriv ℝ k (fun x : ESpace => BSum aSel (t, x)) x‖ ≤ c * (1 - t) ^ (-β)) :
    VorticityRateBound (uSel aSel) := by
  have hcl : 0 ≤ ‖curlLinear‖ := by positivity
  have hcA : 0 ≤ (4 : ℝ) * ‖curlLinear‖ ^ 2 * cutJetBound * c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (pow_nonneg hcl 2)) cutJetBound_nonneg) hc
  have hcB : 0 ≤ (2 : ℝ) * ‖curlLinear‖ * cutJetBound * c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcl)
      cutJetBound_nonneg) hc
  refine vorticityRateBound_sel_of_cylSums (β := β) hcA hcB ht₀ hv hAs hBs ?_ ?_
  · intro t ht
    exact cutVelocity_cylSup_le_rawJets ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans (ht₀.1.trans ht.1), ht.2⟩
      (hAs t ht) hc (hjetA t ht)
  · intro t ht
    exact cutPotential_cylSup_le_rawJets ⟨(show (0 : ℝ) ≤ 3 / 4 by norm_num).trans (ht₀.1.trans ht.1), ht.2⟩
      (hBs t ht) hc (hjetB t ht)

/-- Restricting an `n`-linear form on a product space to the spatial inclusion
`ContinuousLinearMap.inr ℝ ℝ X` does not increase its operator norm: `‖inr‖ ≤ 1`,
so the `n`-fold product of its norm in
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le` is at most `1`. -/
theorem norm_compContinuousLinearMap_inr_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (φ : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × X) W) :
    ‖φ.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ X)‖ ≤ ‖φ‖ := by
  classical
  have hprod : ∏ _ : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ X‖ ≤ (1 : ℝ) := by
    rw [Fin.prod_const n ‖ContinuousLinearMap.inr ℝ ℝ X‖]
    exact pow_le_one₀ (norm_nonneg _)
      (ContinuousLinearMap.norm_inr_le_one ℝ ℝ X)
  calc ‖φ.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ X)‖
      ≤ ‖φ‖ * ∏ _ : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ X‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖φ‖ := mul_one _

open scoped Pointwise in
/-- **(Spacetime jets bound spatial slice jets.)** The raw slice-jet hypotheses
`hjetA`, `hjetB` of `cutVelocity_cylSup_le_rawJets` and
`cutPotential_cylSup_le_rawJets` ask for the iterated derivative of a TIME SLICE
`fun x => f (t, x)`, while the Construction-side summation
`CS_PotentialSumEnvelope.potentialSum_negPower_envelope` bounds the SPACETIME
jet `iteratedFDeriv ℝ n f (t, x)`. This is the bridge between the two formats:
the slice's `n`-jet is the spacetime `n`-jet restricted to the spatial
inclusion `ContinuousLinearMap.inr ℝ ℝ X`, which is norm-nonincreasing
(`norm_compContinuousLinearMap_inr_le`), so the restriction cannot increase the
operator norm.

Smoothness is needed only on an open set `s` that contains the whole slice
`{p | p.1 = t}` — the shape the Construction side actually records, where the
potential sums are smooth on `PhysicalWaveSum.preterminal` and never on all of
spacetime. The identity factors the slice as
`f ∘ ((t, 0) + ·) ∘ inr` and combines
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` with the translation
invariance `iteratedFDerivWithin_comp_add_left`, then drops the restriction with
`iteratedFDerivWithin_of_isOpen`, exactly as
`BKMLogBootstrap.iteratedFDeriv_slice_eq_within_compContinuousLinearMap` does
for the joint half-space smoothness of a sliced solution. No PDE input. -/
theorem norm_iteratedFDeriv_slice_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ × X → W) {s : Set (ℝ × X)} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (t : ℝ) (ht : ∀ y : X, (t, y) ∈ s) (x : X) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : X => f (t, y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (t, x)‖ := by
  classical
  set a : ℝ × X := (t, 0) with hadef
  set σ : Set (ℝ × X) := (fun z : ℝ × X => a + z) ⁻¹' s with hσdef
  have hinr : ∀ y : X, a + ContinuousLinearMap.inr ℝ ℝ X y = (t, y) := by
    intro y
    rw [hadef, ContinuousLinearMap.inr_apply, Prod.mk_add_mk]
    simp
  have hmem : ∀ y : X, ContinuousLinearMap.inr ℝ ℝ X y ∈ σ := by
    intro y
    rw [hσdef, Set.mem_preimage]
    rw [hinr y]
    exact ht y
  have hpre : (ContinuousLinearMap.inr ℝ ℝ X) ⁻¹' σ = Set.univ := eq_univ_of_forall hmem
  have hσo : IsOpen σ := IsOpen.preimage (continuous_const.add continuous_id) hs
  have hfun : ((fun z : ℝ × X => f (a + z)) ∘ ContinuousLinearMap.inr ℝ ℝ X) =
      fun y : X => f (t, y) := by
    funext y
    exact congrArg f (hinr y)
  have hshift : iteratedFDerivWithin ℝ n (fun z : ℝ × X => f (a + z)) σ
      (ContinuousLinearMap.inr ℝ ℝ X x)
      = iteratedFDerivWithin ℝ n f (a +ᵥ σ) (a + ContinuousLinearMap.inr ℝ ℝ X x) := by
    simpa [Function.comp_def] using
      (iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := f) (s := σ) n a
        (ContinuousLinearMap.inr ℝ ℝ X x))
  have hσs : a +ᵥ σ = s := by
    rw [hσdef]
    ext z
    constructor
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨z - a, by simpa using hz, by simp [vadd_eq_add]⟩
  have hsmoothσ : ContDiffOn ℝ ∞ (fun z : ℝ × X => f (a + z)) σ :=
    hf.comp (contDiffOn_const.add contDiffOn_id)
      (fun z hz => by rw [hσdef, Set.mem_preimage] at hz; exact hz)
  have hcomp := (ContinuousLinearMap.inr ℝ ℝ X).iteratedFDerivWithin_comp_right
    hsmoothσ hσo.uniqueDiffOn (by rw [hpre]; exact uniqueDiffOn_univ) (hmem x)
      (show n ≤ ∞ from mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_univ, hfun, hshift, hσs, hinr] at hcomp
  have hplain : iteratedFDerivWithin ℝ n f s (t, x) = iteratedFDeriv ℝ n f (t, x) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (s := s) n hs (ht x)
  rw [hplain] at hcomp
  calc ‖iteratedFDeriv ℝ n (fun y : X => f (t, y)) x‖
      = ‖(iteratedFDeriv ℝ n f (t, x)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ X)‖ := by rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n f (t, x)‖ := norm_compContinuousLinearMap_inr_le n _

end Navier.Analysis.BKMEnvCut

#check @Navier.Analysis.BKMEnvCut.slice_eq_late
#print axioms Navier.Analysis.BKMEnvCut.slice_eq_late
#check @Navier.Analysis.BKMEnvCut.V_velocity_eq_sup_cyl
#print axioms Navier.Analysis.BKMEnvCut.V_velocity_eq_sup_cyl
#check @Navier.Analysis.BKMEnvCut.V_velocity_le_cylSums
#print axioms Navier.Analysis.BKMEnvCut.V_velocity_le_cylSums
#check @Navier.Analysis.BKMEnvCut.polyUpper_of_cylSums
#print axioms Navier.Analysis.BKMEnvCut.polyUpper_of_cylSums
#check @Navier.Analysis.BKMEnvCut.vorticityRateBound_sel_of_cylSums
#print axioms Navier.Analysis.BKMEnvCut.vorticityRateBound_sel_of_cylSums
#check @Navier.Analysis.BKMEnvCut.cutJetBound
#print axioms Navier.Analysis.BKMEnvCut.cutJetBound
#check @Navier.Analysis.BKMEnvCut.cutVelocity_cylSup_le_rawJets
#print axioms Navier.Analysis.BKMEnvCut.cutVelocity_cylSup_le_rawJets
#check @Navier.Analysis.BKMEnvCut.cutPotential_cylSup_le_rawJets
#print axioms Navier.Analysis.BKMEnvCut.cutPotential_cylSup_le_rawJets
#check @Navier.Analysis.BKMEnvCut.vorticityRateBound_sel_of_rawJets
#print axioms Navier.Analysis.BKMEnvCut.vorticityRateBound_sel_of_rawJets
#check @Navier.Analysis.BKMEnvCut.norm_compContinuousLinearMap_inr_le
#print axioms Navier.Analysis.BKMEnvCut.norm_compContinuousLinearMap_inr_le
#check @Navier.Analysis.BKMEnvCut.norm_iteratedFDeriv_slice_le
#print axioms Navier.Analysis.BKMEnvCut.norm_iteratedFDeriv_slice_le
