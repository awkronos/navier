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
   (hypotheses `hAs`, `hBs`); the Leibniz decomposition of the two cut curls
   into RAW stage sups is transport 3, which this module does NOT prove.
4. `polyUpper_of_cylSums` and `vorticityRateBound_sel_of_cylSums` — the
   envelope consumer: two power-law bounds (one rate `β`) on the two
   cylinder sups feed `BKMEnvAxis.vorticityRateBound_sel_of_polyUpper`,
   advancing the single named `hup` hypothesis of the selected-field bridge
   to the two named cylinder-sup obligations.

WHAT THIS MODULE DOES NOT PROVE: it does not discharge `VorticityRateBound
(uSel aSel)` — the two cylinder-sup envelope hypotheses are live obligations
(the remaining T1–T3 transports), and this module's crown corollary is
conditional on them. No status prose elsewhere is superseded by this file.
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
