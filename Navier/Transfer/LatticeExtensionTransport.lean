import Navier.Analysis.ContinuousLeiLinDissipation
import Navier.Analysis.ContinuousLeiLinPressureReconstruction
import Navier.Analysis.CriticalMildWeightedBanach
import Navier.Analysis.FourierMajorant

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Lattice → whole-space transport bridge: the cell extension

FALSIFICATION_LEDGER F-008 quarantines any coercion from the periodic carrier
`B` to the whole-space carrier `A`, permitting as its successor a theorem
transporting datum, decay, pressure and energy field by field.
`PeriodicRealizationSchwartzObstruction` kernel-falsified the naive form
(reading the periodic physical realization as a whole-space velocity; witness
`rotationalDatum`) and named the replacement: a NON-periodic whole-space
carrier. This file supplies the successor: an explicit transport map from the
exact lattice carrier `WeightedLatticeBanach` (the source of
`CriticalMildSmallDataGlobal.smallDataGlobalMild`) to the exact continuous
carrier `ES → ComplexSpace` of `ContinuousLeiLinSpace`, with every budget the
continuous assembly consumes transported field by field, side conditions
visible, no premise laundering.

The map is the cell extension: over the half-open unit cube
`piCell m = {x | ∀ i, latVec m i − 1/2 ≤ x i < latVec m i + 1/2}` — which
tiles `ℝ³` exactly (`piCell_covers`, `piCell_disjoint`) — the extended field
carries the decoded coefficient `weightedLatticeCoefficient u m`. This is
genuinely non-periodic: `x` and `x + eᵢ` generally index different cells.

Design B: all cell arithmetic happens on plain `Space := Fin 3 → ℝ` with the
pulled-back Euclidean frequency norm `normE x := ‖WithLp.toLp 2 x‖`; the `ES`
side is the `spaceProj`-composition, so integrals transport by
`FourierMajorant.integral_spaceProj` and integrability by
`PiLp.volume_preserving_toLp.integrable_comp_emb` (the `.mp` direction).

Transported field by field: datum class (per-coordinate a.e. strong
measurability and integrability premises); decay budgets `X⁰ ≤ ‖u‖`,
`X¹ ≤ C₁‖u‖` (cell diameter √3/2), `X⁻¹ ≤ Cm‖u‖` (nonzero cells) plus the
explicit singular ball integral at the origin cell (`Cm = singularCellMass + 16`
finite by the `rpow` criterion); the named headline quantity, the `X¹` budget
`coordinateX1Mass (latticeExtension u) ≤ 3·C₁·‖u‖`, and its image under the
peer heat chain; the per-coordinate `L²` datum energy; and the bilinear,
pressure and pressure-gradient feeds. No transversality transport is claimed:
`WeightedLatticeBanach` carries no divergence-free field to transport (its
elements are plain `lp (fun _ => ComplexE3) 1` summable coefficient fields).

Honest boundary: the full mild self-map spacetime integrability (peer time
leaves `hmX1`, `ContinuousLeiLinMildAssemblyLeaves`, Fourier-lattice row of
`docs/OPEN_FRONTIER_MAP.md`) is NOT proved here — it is declared as the open
obligation `MildSelfMapTransport` and nothing above depends on it. Peer-owned
continuous files are untouched; this is the first owner of `Navier/Transfer/`.
-/

noncomputable section

namespace Navier.Transfer.LatticeExtensionTransport

open MeasureTheory Set BigOperators Filter Topology
open scoped ENNReal
open Navier
open Navier.Analysis
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinPressureReconstruction
open Navier.Analysis.FourierMajorant

/-! ## Pulled-back frequency norm and the cell tiling on `Space` -/

/-- The lattice mode point as a plain frequency. -/
abbrev latVec (m : LatticeMode) : Space := latticeFrequency m

/-- The Euclidean frequency norm pulled back to plain `Space`. -/
noncomputable def normE (x : Space) : ℝ := ‖WithLp.toLp 2 x‖

@[simp] theorem normE_spaceProj (ξ : ES) : normE (spaceProj ξ) = ‖ξ‖ := rfl

theorem spaceProj_toLp (x : Space) : spaceProj (WithLp.toLp 2 x) = x := by
  ext i; rfl

@[simp] theorem latVec_fst (m : LatticeMode) : latVec m 0 = (m.1 : ℝ) := rfl
@[simp] theorem latVec_snd_fst (m : LatticeMode) : latVec m 1 = (m.2.1 : ℝ) := rfl
@[simp] theorem latVec_snd_snd (m : LatticeMode) : latVec m 2 = (m.2.2 : ℝ) := rfl

/-- The half-open unit cell with mode corner `m`. -/
def piCell (m : LatticeMode) : Set Space :=
  Set.pi Set.univ fun i => Set.Ico (latVec m i - 1 / 2) (latVec m i + 1 / 2)

/-- The index of the unit cell containing a plain frequency. -/
def cellIndexSpace (x : Space) : LatticeMode :=
  (Int.floor (x 0 + 1 / 2), (Int.floor (x 1 + 1 / 2), Int.floor (x 2 + 1 / 2)))

/-- Exact tiling property: `x` lies in `piCell m` iff `m` is its cell index. -/
theorem mem_piCell (m : LatticeMode) (x : Space) :
    x ∈ piCell m ↔ cellIndexSpace x = m := by
  constructor
  · intro h
    rcases m with ⟨a, b, c⟩
    simp only [piCell, Set.mem_pi] at h
    have h0 : ⌊x 0 + 1 / 2⌋ = a := by
      have hx := h 0 (Set.mem_univ 0)
      rw [mem_Ico, latVec_fst] at hx
      obtain ⟨l, r⟩ := hx
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have h1 : ⌊x 1 + 1 / 2⌋ = b := by
      have hx := h 1 (Set.mem_univ 1)
      rw [mem_Ico, latVec_snd_fst] at hx
      obtain ⟨l, r⟩ := hx
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have h2 : ⌊x 2 + 1 / 2⌋ = c := by
      have hx := h 2 (Set.mem_univ 2)
      rw [mem_Ico, latVec_snd_snd] at hx
      obtain ⟨l, r⟩ := hx
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    show (⌊x 0 + 1 / 2⌋, (⌊x 1 + 1 / 2⌋, ⌊x 2 + 1 / 2⌋)) = (a, (b, c))
    rw [h0, h1, h2]
  · intro h
    rcases m with ⟨a, b, c⟩
    show x ∈ Set.pi Set.univ
      fun i => Set.Ico (latVec (a, (b, c)) i - 1 / 2) (latVec (a, (b, c)) i + 1 / 2)
    refine Set.mem_pi.mpr fun i _ => ?_
    simp only [cellIndexSpace, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    fin_cases i
    · rw [mem_Ico]
      show (a : ℝ) - 1 / 2 ≤ x 0 ∧ x 0 < (a : ℝ) + 1 / 2
      obtain ⟨l, r⟩ := Int.floor_eq_iff.mp h0
      exact ⟨by linarith, by linarith⟩
    · rw [mem_Ico]
      show (b : ℝ) - 1 / 2 ≤ x 1 ∧ x 1 < (b : ℝ) + 1 / 2
      obtain ⟨l, r⟩ := Int.floor_eq_iff.mp h1
      exact ⟨by linarith, by linarith⟩
    · rw [mem_Ico]
      show (c : ℝ) - 1 / 2 ≤ x 2 ∧ x 2 < (c : ℝ) + 1 / 2
      obtain ⟨l, r⟩ := Int.floor_eq_iff.mp h2
      exact ⟨by linarith, by linarith⟩

/-- Every frequency lies in its indexed cell. -/
theorem piCell_covers (x : Space) : x ∈ piCell (cellIndexSpace x) :=
  (mem_piCell (cellIndexSpace x) x).mpr rfl

/-- Distinct cells are disjoint. -/
theorem piCell_disjoint {m n : LatticeMode} (h : m ≠ n) :
    Disjoint (piCell m) (piCell n) := by
  refine Set.disjoint_left.mpr fun x hx hx' => h ?_
  exact ((mem_piCell m x).mp hx).symm.trans ((mem_piCell n x).mp hx')

theorem measurableSet_piCell (m : LatticeMode) : MeasurableSet (piCell m) := by
  unfold piCell
  refine MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ico

theorem volume_piCell (m : LatticeMode) : volume (piCell m) = 1 := by
  have h1 : ∀ a : ℝ, volume (Set.Ico (a - 1 / 2) (a + 1 / 2)) = 1 := by
    intro a
    rw [Real.volume_Ico]
    have hsub : (a + 1 / 2) - (a - 1 / 2) = (1 : ℝ) := by ring
    rw [hsub, ENNReal.ofReal_one]
  unfold piCell
  rw [volume_pi_pi]
  exact Finset.prod_eq_one fun i _ => h1 (latVec m i)

private theorem piCell_zero_subset_ball :
    piCell 0 ⊆ Metric.closedBall (0 : Space) 1 := by
  intro x hx
  have hidx := (mem_piCell (0 : LatticeMode) x).mp hx
  have h0f : ⌊x 0 + 1 / 2⌋ = (0 : ℤ) := congr_arg Prod.fst hidx
  have h1f : ⌊x 1 + 1 / 2⌋ = (0 : ℤ) := congr_arg (fun p : LatticeMode => p.2.1) hidx
  have h2f : ⌊x 2 + 1 / 2⌋ = (0 : ℤ) := congr_arg (fun p : LatticeMode => p.2.2) hidx
  have hc0 : |x 0| ≤ 1 / 2 := by
    rw [Int.floor_eq_iff] at h0f
    obtain ⟨l, r⟩ := h0f
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc1 : |x 1| ≤ 1 / 2 := by
    rw [Int.floor_eq_iff] at h1f
    obtain ⟨l, r⟩ := h1f
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc2 : |x 2| ≤ 1 / 2 := by
    rw [Int.floor_eq_iff] at h2f
    obtain ⟨l, r⟩ := h2f
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : ‖x‖ ≤ 1 / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr fun i => ?_
    fin_cases i
    · simpa using hc0
    · simpa using hc1
    · simpa using hc2
  simpa [dist_eq_norm, sub_zero] using hn.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)

/-! ## Geometry: `normE` is the pulled-back Euclidean norm -/

private def toLpLin : Space →ₗ[ℝ] ES :=
  ((EuclideanSpace.equiv (Fin 3) ℝ).symm : Space →ₗ[ℝ] ES)

private theorem toLpLin_apply (x : Space) : toLpLin x = WithLp.toLp 2 x := rfl

theorem normE_def (x : Space) : normE x = ‖WithLp.toLp 2 x‖ := rfl

theorem normE_nonneg (x : Space) : 0 ≤ normE x := by
  unfold normE; exact norm_nonneg _

theorem normE_neg (x : Space) : normE (-x) = normE x := by
  unfold normE
  rw [← toLpLin_apply, map_neg (f := toLpLin)]
  exact norm_neg _

theorem normE_triangle (x y : Space) : normE (x + y) ≤ normE x + normE y := by
  unfold normE
  rw [← toLpLin_apply, map_add (f := toLpLin)]
  exact norm_add_le _ _

private theorem norm_coord_le_norm {𝕜 : Type*} [RCLike 𝕜]
    (z : EuclideanSpace 𝕜 (Fin 3)) (i : Fin 3) : ‖z i‖ ≤ ‖z‖ := by
  have hs : ‖z i‖ ^ 2 ≤ ∑ j : Fin 3, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hsum : ∑ j : Fin 3, ‖z j‖ ^ 2 = ‖z‖ ^ 2 :=
    by rw [EuclideanSpace.norm_sq_eq]
  calc ‖z i‖ = Real.sqrt (‖z i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt (hs.trans hsum.le)
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_pi_le_normE (x : Space) : ‖x‖ ≤ normE x := by
  unfold normE
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  simpa using norm_coord_le_norm (WithLp.toLp 2 x) i

theorem normE_inv_le_normInv (x : Space) : (normE x)⁻¹ ≤ ‖x‖⁻¹ := by
  by_cases hz : x = 0
  · subst hz; simp [normE]
  · exact inv_anti₀ (norm_pos_iff.mpr hz) (norm_pi_le_normE x)

theorem measurable_normE : Measurable normE := by
  unfold normE
  exact ((MeasurableEquiv.toLp (p := (2 : ℝ≥0∞)) (X := Space)).measurable).norm

theorem aestm_normE_inv :
    AEStronglyMeasurable (fun x : Space => (normE x)⁻¹) volume :=
  (measurable_normE.aestronglyMeasurable).inv₀

theorem normE_latVec_eq_weight (m : LatticeMode) :
    normE (latVec m) = ‖complexFrequency (latticeFrequency m)‖ := by
  have hsq : normE (latVec m) ^ 2 = ‖complexFrequency (latticeFrequency m)‖ ^ 2 := by
    unfold normE
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    show ‖latVec m i‖ ^ 2 = ‖complexFrequency (latVec m) i‖ ^ 2
    rw [complexFrequency_apply]
    rw [Complex.norm_real]
  calc normE (latVec m) = Real.sqrt (normE (latVec m) ^ 2) :=
      (Real.sqrt_sq (normE_nonneg _)).symm
    _ = Real.sqrt (‖complexFrequency (latticeFrequency m)‖ ^ 2) := by rw [hsq]
    _ = ‖complexFrequency (latticeFrequency m)‖ := Real.sqrt_sq (norm_nonneg _)

/-- Inside a cell the frequency lies within `√3/2` of the mode point. -/
theorem normE_sub_latVec_le (m : LatticeMode) (x : Space) (h : x ∈ piCell m) :
    normE (x - latVec m) ≤ Real.sqrt 3 / 2 := by
  have hcoord : ∀ i : Fin 3, |x i - latVec m i| ≤ 1 / 2 := by
    intro i
    have hx := Set.mem_pi.1 h i (Set.mem_univ i)
    rw [mem_Ico] at hx
    obtain ⟨lft, rgt⟩ := hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq : normE (x - latVec m) ^ 2 ≤ 3 / 4 := by
    unfold normE
    rw [EuclideanSpace.norm_sq_eq]
    have hsum4 : ∑ i : Fin 3, (1 / 4 : ℝ) = 3 / 4 := by
      rw [Finset.sum_const, Finset.card_univ]
      norm_num
    rw [← hsum4]
    refine Finset.sum_le_sum fun i _ => ?_
    show ‖(x - latVec m) i‖ ^ 2 ≤ (1 / 4 : ℝ)
    rw [Real.norm_eq_abs]
    have hsub2 : (x - latVec m) i = x i - latVec m i := rfl
    rw [hsub2]
    have hprod : |x i - latVec m i| * |x i - latVec m i| ≤ (1 / 2 : ℝ) * (1 / 2) :=
      mul_le_mul (hcoord i) (hcoord i) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← pow_two, ← pow_two] at hprod
    rw [show ((1 / 2 : ℝ)) ^ 2 = 1 / 4 by norm_num] at hprod
    exact hprod
  calc normE (x - latVec m) = Real.sqrt (normE (x - latVec m) ^ 2) :=
      (Real.sqrt_sq (normE_nonneg _)).symm
    _ ≤ Real.sqrt (3 / 4) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num

/-! ## Weight control and the two-sided mass budget -/

private theorem one_le_norm_coe_int (k : ℤ) (hk : k ≠ 0) : (1 : ℝ) ≤ ‖(k : ℝ)‖ := by
  by_cases hpos : (0 : ℤ) ≤ k
  · have hk1 : (1 : ℤ) ≤ k := by omega
    have h2 : ‖(k : ℝ)‖ = (k : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hpos)]
    rw [h2]
    exact_mod_cast hk1
  · have hneg : k < 0 := by omega
    have hk1 : (1 : ℤ) ≤ -k := by omega
    have h2 : ‖(k : ℝ)‖ = (-k : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_neg (by exact_mod_cast hneg)]
    rw [h2]
    exact_mod_cast hk1

/-- Every nonzero lattice mode point is at Euclidean distance at least one
from the origin. -/
theorem normE_latVec_ge_one {m : LatticeMode} (hm : m ≠ 0) : 1 ≤ normE (latVec m) := by
  obtain ⟨a, b, c⟩ := m
  have hnez : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (by simp [h.1, h.2.1, h.2.2])
  rcases hnez with ha | hb | hc
  · refine le_trans (one_le_norm_coe_int a ha) ?_
    show ‖latVec (a, (b, c)) (0 : Fin 3)‖ ≤ ‖WithLp.toLp 2 (latVec (a, (b, c)))‖
    simpa using norm_coord_le_norm (WithLp.toLp 2 (latVec (a, (b, c)))) 0
  · refine le_trans (one_le_norm_coe_int b hb) ?_
    show ‖latVec (a, (b, c)) (1 : Fin 3)‖ ≤ ‖WithLp.toLp 2 (latVec (a, (b, c)))‖
    simpa using norm_coord_le_norm (WithLp.toLp 2 (latVec (a, (b, c)))) 1
  · refine le_trans (one_le_norm_coe_int c hc) ?_
    show ‖latVec (a, (b, c)) (2 : Fin 3)‖ ≤ ‖WithLp.toLp 2 (latVec (a, (b, c)))‖
    simpa using norm_coord_le_norm (WithLp.toLp 2 (latVec (a, (b, c)))) 2

/-- Cell-diameter inflation constant: `√3/2` over the unit weight floor. -/
def C1 : ℝ := 1 + Real.sqrt 3 / 2

/-- On-cell upper weight transport: `‖x‖_E ≤ C1 · w(m(x))`. -/
theorem normE_le_weight_x1 (m : LatticeMode) (x : Space) (h : x ∈ piCell m) :
    normE x ≤ C1 * latticeModeWeight m := by
  have heq : x = latVec m + (x - latVec m) := by abel
  have htri : normE x ≤ normE (latVec m) + Real.sqrt 3 / 2 := by
    rw [heq]
    refine le_trans (normE_triangle (latVec m) (x - latVec m)) ?_
    exact add_le_add_right (normE_sub_latVec_le m x h) (normE (latVec m))
  have hw : latticeModeWeight m = 1 + normE (latVec m) := by
    unfold latticeModeWeight
    rw [← normE_latVec_eq_weight]
  unfold C1
  rw [hw]
  nlinarith [htri, normE_nonneg (latVec m), Real.sqrt_nonneg 3]

/-- On-cell lower weight transport off the singular cell:
`(‖x‖_E)⁻¹ ≤ 16 / w(m(x))` for `x` in a nonzero cell. -/
theorem normInv_le_weight_xm1 (m : LatticeMode) (hm : m ≠ 0) (x : Space)
    (h : x ∈ piCell m) : (normE x)⁻¹ ≤ (16 : ℝ) / latticeModeWeight m := by
  set L : ℝ := normE (latVec m) with hLdef
  have hL1 : 1 ≤ L := normE_latVec_ge_one hm
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h83 : (8 : ℝ) * Real.sqrt 3 ≤ 14 := by
    nlinarith [hs3, sq_nonneg (Real.sqrt 3 - 7 / 4)]
  have hLpos : 0 < L - Real.sqrt 3 / 2 := by
    nlinarith [Real.sqrt_nonneg 3, h83, hL1]
  have hWpos : (0 : ℝ) < 1 + L := by nlinarith [hL1]
  have hlow : L - Real.sqrt 3 / 2 ≤ normE x := by
    have hsum : (latVec m - x) + x = latVec m := by abel
    have htri : normE (latVec m - x + x) ≤ normE (latVec m - x) + normE x :=
      normE_triangle (latVec m - x) x
    rw [hsum] at htri
    have hnx : normE (latVec m - x) = normE (x - latVec m) := by
      unfold normE
      have h : WithLp.toLp 2 (latVec m - x) = -(WithLp.toLp 2 (x - latVec m)) := by
        rw [show (latVec m - x : Space) = -(x - latVec m) by abel,
          ← toLpLin_apply (-(x - latVec m)), map_neg (f := toLpLin),
          toLpLin_apply (x - latVec m)]
      rw [h, norm_neg]
    have hsub : normE (x - latVec m) ≤ Real.sqrt 3 / 2 := normE_sub_latVec_le m x h
    rw [← hLdef] at htri
    nlinarith [htri, hnx, hsub]
  have hw : latticeModeWeight m = 1 + L := by
    unfold latticeModeWeight
    rw [← normE_latVec_eq_weight, ← hLdef]
  calc (normE x)⁻¹ ≤ (L - Real.sqrt 3 / 2)⁻¹ := inv_anti₀ hLpos hlow
    _ = 1 / (L - Real.sqrt 3 / 2) := by rw [inv_eq_one_div]
    _ ≤ 16 / latticeModeWeight m := by
        rw [hw]
        have hq : (0 : ℝ) < 2 * L - Real.sqrt 3 := by
          nlinarith [hL1, h83]
        have hden : L - Real.sqrt 3 / 2 = (2 * L - Real.sqrt 3) / 2 := by ring
        rw [hden]
        field_simp
        nlinarith [hL1, h83]

/-- The only cell whose inverse-frequency integral cannot be bounded
pointwise: the singular cell mass `∫_{|x|≤1} ‖x‖_E⁻¹`. -/
noncomputable def singularCellMass : ℝ :=
  ∫ x : Space in Metric.closedBall (0 : Space) 1, (normE x)⁻¹

theorem integrable_normInv_ball :
    Integrable (fun x : Space => (normE x)⁻¹)
      (volume.restrict (Metric.closedBall (0 : Space) 1)) := by
  have hlocal : LocallyIntegrable (fun x : Space => (normE x)⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (μ := volume) (E := Space) (F := ℝ)
      (by norm_num) (C := (1 : ℝ)) (α := (1 : ℝ)) (by norm_num) ?_ ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (normE_nonneg x)),
        one_mul]
      have h2 : ‖x‖ ^ (-(1 : ℝ)) = ‖x‖⁻¹ := Real.rpow_neg_one _
      rw [h2]
      exact normE_inv_le_normInv x
    · exact aestm_normE_inv
  exact hlocal.integrableOn_isCompact (isCompact_closedBall (0 : Space) 1)

theorem singularCellMass_nonneg : 0 ≤ singularCellMass := by
  unfold singularCellMass
  refine integral_nonneg fun x => inv_nonneg.mpr (normE_nonneg x)

/-- The `X⁻¹` cell budget: singular-cell mass plus the off-singular
pointwise constant `16`. -/
def Cm : ℝ := singularCellMass + 16

theorem Cm_nonneg : 0 ≤ Cm := by
  unfold Cm
  nlinarith [singularCellMass_nonneg]

theorem C1_nonneg : 0 ≤ C1 := by
  unfold C1
  nlinarith [Real.sqrt_nonneg 3]

theorem Cm_ge_singular : singularCellMass ≤ Cm := by
  unfold Cm
  linarith

theorem Cm_ge_sixteen : (16 : ℝ) ≤ Cm := by
  unfold Cm
  linarith [singularCellMass_nonneg]

/-! ## The cell extension map -/

/-- The successor field on plain frequencies: over `piCell m` it carries the
decoded coefficient of mode `m`. -/
noncomputable def latticeExtensionSpace (u : WeightedLatticeBanach) (x : Space) :
    ComplexSpace :=
  weightedLatticeCoefficient u (cellIndexSpace x)

/-- The A-carrier lattice extension: pull back along `spaceProj`. -/
noncomputable def latticeExtension (u : WeightedLatticeBanach) (ξ : ES) : ComplexSpace :=
  latticeExtensionSpace u (spaceProj ξ)

theorem latticeExtensionSpace_apply (u : WeightedLatticeBanach) (x : Space) (j : Fin 3) :
    latticeExtensionSpace u x j = weightedLatticeCoefficient u (cellIndexSpace x) j := rfl

theorem latticeExtension_apply (u : WeightedLatticeBanach) (ξ : ES) (j : Fin 3) :
    latticeExtension u ξ j = weightedLatticeCoefficient u (cellIndexSpace (spaceProj ξ)) j := rfl

/-- Coordinate decay of the decoded coefficient: weighted `‖u m‖ / w m`. -/
theorem coeff_coord_le_weight (u : WeightedLatticeBanach) (m : LatticeMode) (j : Fin 3) :
    ‖weightedLatticeCoefficient u m j‖ ≤ ‖u m‖ / latticeModeWeight m := by
  have hpos : 0 < latticeModeWeight m :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m)
  have h1 : ‖weightedLatticeCoefficient u m j‖ ≤
      complexEuclideanNorm (weightedLatticeCoefficient u m) := by
    have key : ‖weightedLatticeCoefficient u m j‖ ≤
        ‖complexEuclideanPoint (weightedLatticeCoefficient u m)‖ := by
      simpa [complexEuclideanPoint_apply] using
        norm_coord_le_norm (complexEuclideanPoint (weightedLatticeCoefficient u m)) j
    exact key
  have hamp : latticeModeWeight m * complexEuclideanNorm (weightedLatticeCoefficient u m) =
      ‖u m‖ := by
    have := latticeWeightedAmplitude_coefficient u m
    rwa [latticeWeightedAmplitude] at this
  calc ‖weightedLatticeCoefficient u m j‖
      ≤ complexEuclideanNorm (weightedLatticeCoefficient u m) := h1
    _ = ‖u m‖ / latticeModeWeight m :=
        (eq_div_iff hpos.ne').mpr (by rw [mul_comm]; exact hamp)

/-- Plain coordinate decay of the decoded coefficient. -/
theorem coeff_coord_le (u : WeightedLatticeBanach) (m : LatticeMode) (j : Fin 3) :
    ‖weightedLatticeCoefficient u m j‖ ≤ ‖u m‖ := by
  calc ‖weightedLatticeCoefficient u m j‖
      ≤ ‖u m‖ / latticeModeWeight m := coeff_coord_le_weight u m j
    _ ≤ ‖u m‖ := div_le_self (norm_nonneg _) (one_le_latticeModeWeight m)

/-- The coefficient sequence of a carrier member is summable in norm, with
total the carrier norm. -/
theorem summable_norm_u (u : WeightedLatticeBanach) :
    Summable (fun m : LatticeMode => ‖u m‖) := by
  have hfun : latticeWeightedAmplitude (weightedLatticeCoefficient u) =
      fun m : LatticeMode => ‖u m‖ := by
    funext m
    exact latticeWeightedAmplitude_coefficient u m
  rw [← hfun]
  exact latticeWeightedL1_coefficient u

theorem tsum_norm_u (u : WeightedLatticeBanach) : (∑' m, ‖u m‖) = ‖u‖ := by
  refine Eq.trans ?_ (tsum_latticeWeightedAmplitude_coefficient u)
  congr 1
  funext m
  exact (latticeWeightedAmplitude_coefficient u m).symm

/-! ## Measurability of the extension -/

private theorem measurable_coefficientCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Measurable (fun m : LatticeMode => weightedLatticeCoefficient u m j) :=
  measurable_of_countable _

theorem measurable_cellIndexSpace : Measurable cellIndexSpace := by
  show Measurable fun x : Space =>
    (Int.floor (x 0 + 1 / 2), (Int.floor (x 1 + 1 / 2), Int.floor (x 2 + 1 / 2)))
  refine Measurable.prod ?_ (Measurable.prod ?_ ?_)
  all_goals
    refine Int.measurable_floor.comp ?_
    exact ((continuous_apply _).measurable.add continuous_const.measurable)

theorem measurable_latticeExtensionSpaceCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Measurable (fun x : Space => latticeExtensionSpace u x j) :=
  (measurable_coefficientCoord u j).comp measurable_cellIndexSpace

theorem aestm_latticeExtensionCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES => latticeExtension u ξ j) volume :=
  ((measurable_latticeExtensionSpaceCoord u j).comp
      spaceProj.continuous.measurable).aestronglyMeasurable

/-! ## Cell tiling and the lintegral decomposition -/

theorem iUnion_piCell : (⋃ m : LatticeMode, (piCell m : Set Space)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ]
  exact ⟨fun _ => trivial, fun _ => ⟨cellIndexSpace x, piCell_covers x⟩⟩

/-- The lintegral over `Space` decomposes into the cells. -/
theorem lintegral_piCell_tsum (g : Space → ℝ≥0∞) :
    ∫⁻ x : Space, g x = ∑' m : LatticeMode, ∫⁻ x in piCell m, g x := by
  classical
  have hu : (∫⁻ x, g x ∂volume) = ∫⁻ x in Set.univ, g x := by
    calc (∫⁻ x, g x ∂volume)
        = ∫⁻ x, (Set.univ : Set Space).indicator g x ∂volume :=
            congr_arg (fun F : Space → ℝ≥0∞ => ∫⁻ x, F x ∂volume)
              ((funext fun x => indicator_of_mem (Set.mem_univ x) g).symm)
      _ = ∫⁻ x in Set.univ, g x := lintegral_indicator MeasurableSet.univ g
  rw [hu, ← iUnion_piCell]
  refine lintegral_iUnion (fun m => measurableSet_piCell m) ?_ g
  · intro m n hmn
    exact piCell_disjoint hmn

/-- A function dominated by `C` on a cell has cell-lintegral at most `C`
(since every cell has volume one). -/
private theorem lintegral_piCell_le_const (m : LatticeMode) (f : Space → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ x ∈ piCell m, f x ≤ C) : ∫⁻ x in piCell m, f x ≤ C := by
  calc (∫⁻ x in piCell m, f x)
      = ∫⁻ x, (piCell m).indicator f x :=
          (lintegral_indicator (measurableSet_piCell m) f).symm
      _ ≤ ∫⁻ x, (piCell m).indicator (fun _ => C) x :=
          lintegral_mono fun x => by
            by_cases hx : x ∈ piCell m
            · rw [indicator_of_mem hx, indicator_of_mem hx]
              exact h x hx
            · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      _ = C * volume (piCell m) := lintegral_indicator_const (measurableSet_piCell m) C
      _ = C := by rw [volume_piCell m, mul_one]

/-! ## Pointwise cell integrand bounds -/

theorem x1Integrand_piCell_le (u : WeightedLatticeBanach) (m : LatticeMode) (j : Fin 3)
    (x : Space) (hx : x ∈ piCell m) :
    normE x * ‖latticeExtensionSpace u x j‖ ≤ C1 * ‖u m‖ := by
  have hpos : 0 < latticeModeWeight m :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m)
  have hidx : cellIndexSpace x = m := (mem_piCell m x).mp hx
  have hext : ‖latticeExtensionSpace u x j‖ = ‖weightedLatticeCoefficient u m j‖ := by
    rw [latticeExtensionSpace_apply, hidx]
  rw [hext]
  calc normE x * ‖weightedLatticeCoefficient u m j‖
      ≤ normE x * (‖u m‖ / latticeModeWeight m) :=
        mul_le_mul_of_nonneg_left (coeff_coord_le_weight u m j) (normE_nonneg x)
    _ ≤ C1 * latticeModeWeight m * (‖u m‖ / latticeModeWeight m) :=
        mul_le_mul_of_nonneg_right (normE_le_weight_x1 m x hx)
          (div_nonneg (norm_nonneg _) (le_of_lt hpos))
    _ = C1 * ‖u m‖ := by
        field_simp [hpos.ne']

theorem xm1Integrand_piCell_le (u : WeightedLatticeBanach) (m : LatticeMode) (hm : m ≠ 0)
    (j : Fin 3) (x : Space) (hx : x ∈ piCell m) :
    (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ ≤ 16 * ‖u m‖ := by
  have hpos : 0 < latticeModeWeight m :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m)
  have hidx : cellIndexSpace x = m := (mem_piCell m x).mp hx
  have h1 : (normE x)⁻¹ ≤ 16 / latticeModeWeight m := normInv_le_weight_xm1 m hm x hx
  have h2 : ‖latticeExtensionSpace u x j‖ ≤ ‖u m‖ := by
    rw [latticeExtensionSpace_apply, hidx]
    exact coeff_coord_le u m j
  calc (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖
      ≤ (16 / latticeModeWeight m) * ‖u m‖ :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 16) (le_of_lt hpos))
    _ ≤ 16 * ‖u m‖ := by
        have hrew : (16 / latticeModeWeight m) * ‖u m‖ = 16 * (‖u m‖ / latticeModeWeight m) :=
          by ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left
          (div_le_self (norm_nonneg _) (one_le_latticeModeWeight m))
          (by norm_num : (0 : ℝ) ≤ 16)

theorem lintegral_piCell_zero_normInv_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫⁻ x in piCell 0,
      ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)
      ≤ ENNReal.ofReal (Cm * ‖u 0‖) := by
  have h0c : ∀ x ∈ piCell 0,
      (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ ≤ (normE x)⁻¹ * ‖u 0‖ := by
    intro x hx
    have hidx : cellIndexSpace x = (0 : LatticeMode) := (mem_piCell 0 x).mp hx
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (normE_nonneg x))
    rw [latticeExtensionSpace_apply, hidx]
    exact coeff_coord_le u 0 j
  have hstepA : ∫⁻ x in piCell 0,
      ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)
      ≤ ∫⁻ x in Metric.closedBall (0 : Space) 1, ENNReal.ofReal ((normE x)⁻¹ * ‖u 0‖) := by
    rw [← lintegral_indicator (measurableSet_piCell 0)
        (fun x => ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)),
      ← lintegral_indicator (isCompact_closedBall (0 : Space) 1).isClosed.measurableSet
        (fun x => ENNReal.ofReal ((normE x)⁻¹ * ‖u 0‖))]
    refine lintegral_mono fun x => by
      by_cases hx : x ∈ piCell 0
      · have hbx : x ∈ Metric.closedBall (0 : Space) 1 := piCell_zero_subset_ball hx
        rw [indicator_of_mem hx, indicator_of_mem hbx]
        exact ENNReal.ofReal_le_ofReal (h0c x hx)
      · rw [indicator_of_notMem hx]
        exact zero_le
  have hball : ∫⁻ x in Metric.closedBall (0 : Space) 1, ENNReal.ofReal ((normE x)⁻¹ * ‖u 0‖)
      = ENNReal.ofReal (singularCellMass * ‖u 0‖) := by
    have hint : Integrable (fun x : Space => (normE x)⁻¹ * ‖u 0‖)
        (volume.restrict (Metric.closedBall (0 : Space) 1)) :=
      integrable_normInv_ball.mul_const ‖u 0‖
    have hnn : 0 ≤ᵐ[volume.restrict (Metric.closedBall (0 : Space) 1)]
        fun x : Space => (normE x)⁻¹ * ‖u 0‖ :=
      ae_of_all _ fun x => mul_nonneg (inv_nonneg.mpr (normE_nonneg x)) (norm_nonneg _)
    calc ∫⁻ x in Metric.closedBall (0 : Space) 1, ENNReal.ofReal ((normE x)⁻¹ * ‖u 0‖)
        = ENNReal.ofReal (∫ x in Metric.closedBall (0 : Space) 1, (normE x)⁻¹ * ‖u 0‖) :=
            ((ofReal_integral_eq_lintegral_ofReal hint hnn).symm)
      _ = ENNReal.ofReal (singularCellMass * ‖u 0‖) := by
          congr 1
          exact integral_mul_const (μ := volume.restrict (Metric.closedBall (0 : Space) 1))
            ‖u 0‖ (fun x : Space => (normE x)⁻¹)
  refine le_trans hstepA ?_
  rw [hball]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right Cm_ge_singular (norm_nonneg _))

/-! ## Space-side budget theorems -/

theorem integral_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ x : Space, ‖latticeExtensionSpace u x j‖ ≤ ‖u‖ := by
  have hae : 0 ≤ᵐ[volume] fun x : Space => ‖latticeExtensionSpace u x j‖ :=
    ae_of_all volume fun x => norm_nonneg _
  have hs : AEStronglyMeasurable (fun x : Space => ‖latticeExtensionSpace u x j‖) volume :=
    (measurable_latticeExtensionSpaceCoord u j).norm.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hae hs]
  calc (∫⁻ x, ENNReal.ofReal ‖latticeExtensionSpace u x j‖).toReal
      ≤ (ENNReal.ofReal ‖u‖).toReal :=
          ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top)
            (le_trans (Eq.le (lintegral_piCell_tsum _))
              (le_trans (ENNReal.tsum_le_tsum fun m =>
                  lintegral_piCell_le_const m
                    (fun x => ENNReal.ofReal ‖latticeExtensionSpace u x j‖)
                    (ENNReal.ofReal ‖u m‖)
                    (fun x hx => ENNReal.ofReal_le_ofReal
                      (by
                        rw [latticeExtensionSpace_apply, (mem_piCell m x).mp hx]
                        exact coeff_coord_le u m j)))
                (by
                  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _)
                    (summable_norm_u u), tsum_norm_u u])))
    _ = ‖u‖ := ENNReal.toReal_ofReal (norm_nonneg _)

theorem integral_normE_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ x : Space, normE x * ‖latticeExtensionSpace u x j‖ ≤ C1 * ‖u‖ := by
  have hae : 0 ≤ᵐ[volume] fun x : Space => normE x * ‖latticeExtensionSpace u x j‖ :=
    ae_of_all volume fun x => mul_nonneg (normE_nonneg x) (norm_nonneg _)
  have hs : AEStronglyMeasurable (fun x : Space =>
      normE x * ‖latticeExtensionSpace u x j‖) volume :=
    (measurable_normE.mul (measurable_latticeExtensionSpaceCoord u j).norm).aestronglyMeasurable
  have hsumm : Summable (fun m : LatticeMode => C1 * ‖u m‖) :=
    (summable_norm_u u).mul_left C1
  rw [integral_eq_lintegral_of_nonneg_ae hae hs]
  calc (∫⁻ x, ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖)).toReal
      ≤ (ENNReal.ofReal (C1 * ‖u‖)).toReal :=
          ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top)
            (le_trans (Eq.le (lintegral_piCell_tsum _))
              (le_trans (ENNReal.tsum_le_tsum fun m =>
                  lintegral_piCell_le_const m
                    (fun x => ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖))
                    (ENNReal.ofReal (C1 * ‖u m‖))
                    (fun x hx => ENNReal.ofReal_le_ofReal (x1Integrand_piCell_le u m j x hx)))
                (by
                  rw [← ENNReal.ofReal_tsum_of_nonneg
                    (fun m => mul_nonneg C1_nonneg (norm_nonneg _)) hsumm,
                    tsum_mul_left, tsum_norm_u u])))
    _ = C1 * ‖u‖ := ENNReal.toReal_ofReal (mul_nonneg C1_nonneg (norm_nonneg _))

theorem integral_normInv_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ x : Space, (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ ≤ Cm * ‖u‖ := by
  have hae : 0 ≤ᵐ[volume] fun x : Space => (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ :=
    ae_of_all volume fun x =>
      mul_nonneg (inv_nonneg.mpr (normE_nonneg x)) (norm_nonneg _)
  have hs : AEStronglyMeasurable (fun x : Space =>
      (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖) volume :=
    aestm_normE_inv.mul (measurable_latticeExtensionSpaceCoord u j).norm.aestronglyMeasurable
  have hsumm : Summable (fun m : LatticeMode => Cm * ‖u m‖) :=
    (summable_norm_u u).mul_left Cm
  have hcell {m : LatticeMode} (hm : m ≠ 0) :
      ∫⁻ x in piCell m, ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)
        ≤ ENNReal.ofReal (Cm * ‖u m‖) :=
      le_trans (lintegral_piCell_le_const m
          (fun x => ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖))
          (ENNReal.ofReal (16 * ‖u m‖))
          (fun x hx => ENNReal.ofReal_le_ofReal (xm1Integrand_piCell_le u m hm j x hx)))
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right Cm_ge_sixteen (norm_nonneg _)))
  rw [integral_eq_lintegral_of_nonneg_ae hae hs]
  calc (∫⁻ x, ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)).toReal
      ≤ (ENNReal.ofReal (Cm * ‖u‖)).toReal :=
          ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top)
            (le_trans (Eq.le (lintegral_piCell_tsum _))
              (le_trans
                (ENNReal.tsum_le_tsum
                  (f := fun m : LatticeMode =>
                    ∫⁻ x in piCell m,
                      ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖))
                  (g := fun m : LatticeMode => ENNReal.ofReal (Cm * ‖u m‖))
                  fun m => by
                    by_cases hm : m = 0
                    · subst hm
                      exact lintegral_piCell_zero_normInv_le u j
                    · exact hcell hm)
                (by
                  rw [← ENNReal.ofReal_tsum_of_nonneg
                    (fun m => mul_nonneg Cm_nonneg (norm_nonneg _)) hsumm,
                    tsum_mul_left, tsum_norm_u u])))
    _ = Cm * ‖u‖ := ENNReal.toReal_ofReal (mul_nonneg Cm_nonneg (norm_nonneg _))

/-! ## ES-side transport and the headline budgets -/

/-- `X⁰` coordinate bound of the extension. -/
theorem integral_latticeExtensionCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ ξ : ES, ‖latticeExtension u ξ j‖ ≤ ‖u‖ := by
  calc (∫ ξ : ES, ‖latticeExtension u ξ j‖)
      = ∫ x : Space, ‖latticeExtensionSpace u x j‖ := by
          refine ((integral_congr_ae (ae_of_all volume fun ξ : ES => rfl)).trans
            (integral_spaceProj (fun x : Space => ‖latticeExtensionSpace u x j‖)))
    _ ≤ ‖u‖ := integral_latticeExtensionSpaceCoord_le u j

/-- `X¹` coordinate bound of the extension: the named one-small-step bridge. -/
theorem normX1_latticeExtensionCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    normX1 (fun ξ : ES => latticeExtension u ξ j) ≤ C1 * ‖u‖ := by
  unfold normX1
  calc (∫ ξ : ES, ‖ξ‖ * ‖latticeExtension u ξ j‖)
      = ∫ x : Space, normE x * ‖latticeExtensionSpace u x j‖ := by
          refine ((integral_congr_ae (ae_of_all volume fun ξ : ES => rfl)).trans
            (integral_spaceProj (fun x : Space => normE x * ‖latticeExtensionSpace u x j‖)))
    _ ≤ C1 * ‖u‖ := integral_normE_latticeExtensionSpaceCoord_le u j

/-- `X⁻¹` coordinate bound of the extension. -/
theorem normXm1_latticeExtensionCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    normXm1 (fun ξ : ES => latticeExtension u ξ j) ≤ Cm * ‖u‖ := by
  unfold normXm1
  calc (∫ ξ : ES, ‖ξ‖⁻¹ * ‖latticeExtension u ξ j‖)
      = ∫ x : Space, (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ := by
          refine ((integral_congr_ae (ae_of_all volume fun ξ : ES => rfl)).trans
            (integral_spaceProj
              (fun x : Space => (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)))
    _ ≤ Cm * ‖u‖ := integral_normInv_latticeExtensionSpaceCoord_le u j

/-- Successor field by field (F-008): the `X⁰` mass of the extension is at
most three times the carrier norm. -/
theorem coordinateX0Mass_latticeExtension_le (u : WeightedLatticeBanach) :
    coordinateX0Mass (latticeExtension u) ≤ (3 : ℝ) * ‖u‖ := by
  unfold coordinateX0Mass
  refine le_trans (Finset.sum_le_sum fun i _ => integral_latticeExtensionCoord_le u i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_rfl

/-- Successor field by field (F-008): the `X¹` budget of the extension. This
is the named one-small-step transported quantity. -/
theorem coordinateX1Mass_latticeExtension_le (u : WeightedLatticeBanach) :
    coordinateX1Mass (latticeExtension u) ≤ (3 : ℝ) * C1 * ‖u‖ := by
  unfold coordinateX1Mass
  refine le_trans (Finset.sum_le_sum fun i _ => normX1_latticeExtensionCoord_le u i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  exact le_rfl

/-- Successor field by field (F-008): the `X⁻¹` mass of the extension. -/
theorem coordinateXm1Mass_latticeExtension_le (u : WeightedLatticeBanach) :
    coordinateXm1Mass (latticeExtension u) ≤ (3 : ℝ) * Cm * ‖u‖ := by
  unfold coordinateXm1Mass
  refine le_trans (Finset.sum_le_sum fun i _ => normXm1_latticeExtensionCoord_le u i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  exact le_rfl

/-! ## Pointwise ES ↔ Space reduction and integrability transports -/

theorem latticeExtension_toLp (u : WeightedLatticeBanach) (x : Space) :
    latticeExtension u (WithLp.toLp 2 x) = latticeExtensionSpace u x := by
  unfold latticeExtension
  rw [spaceProj_toLp]

/-- Cell-tiling lintegral bound for the `X⁰` integrand (Space side). -/
theorem lintegral_norm_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫⁻ x : Space, ENNReal.ofReal ‖latticeExtensionSpace u x j‖ ≤ ENNReal.ofReal ‖u‖ := by
  calc (∫⁻ x, ENNReal.ofReal ‖latticeExtensionSpace u x j‖)
      = ∑' m : LatticeMode, ∫⁻ x in piCell m,
          ENNReal.ofReal ‖latticeExtensionSpace u x j‖ :=
          lintegral_piCell_tsum _
      _ ≤ ∑' m : LatticeMode, ENNReal.ofReal ‖u m‖ :=
          ENNReal.tsum_le_tsum fun m =>
            lintegral_piCell_le_const m
              (fun x => ENNReal.ofReal ‖latticeExtensionSpace u x j‖)
              (ENNReal.ofReal ‖u m‖)
              (fun x hx => ENNReal.ofReal_le_ofReal
                (by
                  rw [latticeExtensionSpace_apply, (mem_piCell m x).mp hx]
                  exact coeff_coord_le u m j))
      _ = ENNReal.ofReal (∑' m : LatticeMode, ‖u m‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (summable_norm_u u)).symm
      _ = ENNReal.ofReal ‖u‖ := by rw [tsum_norm_u u]

/-- Cell-tiling lintegral bound for the `X¹` integrand (Space side). -/
theorem lintegral_normE_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫⁻ x : Space, ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖) ≤
      ENNReal.ofReal (C1 * ‖u‖) := by
  have hsumm : Summable (fun m : LatticeMode => C1 * ‖u m‖) :=
    (summable_norm_u u).mul_left C1
  calc (∫⁻ x, ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖))
      = ∑' m : LatticeMode, ∫⁻ x in piCell m,
          ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖) :=
          lintegral_piCell_tsum _
      _ ≤ ∑' m : LatticeMode, ENNReal.ofReal (C1 * ‖u m‖) :=
          ENNReal.tsum_le_tsum fun m =>
            lintegral_piCell_le_const m
              (fun x => ENNReal.ofReal (normE x * ‖latticeExtensionSpace u x j‖))
              (ENNReal.ofReal (C1 * ‖u m‖))
              (fun x hx => ENNReal.ofReal_le_ofReal (x1Integrand_piCell_le u m j x hx))
      _ = ENNReal.ofReal (∑' m : LatticeMode, C1 * ‖u m‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg C1_nonneg (norm_nonneg _))
            hsumm).symm
      _ = ENNReal.ofReal (C1 * ‖u‖) := by rw [tsum_mul_left, tsum_norm_u u]

/-- Cell-tiling lintegral bound for the `X⁻¹` integrand (Space side). -/
theorem lintegral_normInv_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫⁻ x : Space, ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖) ≤
      ENNReal.ofReal (Cm * ‖u‖) := by
  have hsumm : Summable (fun m : LatticeMode => Cm * ‖u m‖) :=
    (summable_norm_u u).mul_left Cm
  have hcell {m : LatticeMode} (hm : m ≠ 0) :
      ∫⁻ x in piCell m, ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖)
        ≤ ENNReal.ofReal (Cm * ‖u m‖) :=
      le_trans (lintegral_piCell_le_const m
          (fun x => ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖))
          (ENNReal.ofReal (16 * ‖u m‖))
          (fun x hx => ENNReal.ofReal_le_ofReal (xm1Integrand_piCell_le u m hm j x hx)))
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right Cm_ge_sixteen (norm_nonneg _)))
  calc (∫⁻ x, ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖))
      = ∑' m : LatticeMode, ∫⁻ x in piCell m,
          ENNReal.ofReal ((normE x)⁻¹ * ‖latticeExtensionSpace u x j‖) :=
          lintegral_piCell_tsum _
      _ ≤ ∑' m : LatticeMode, ENNReal.ofReal (Cm * ‖u m‖) :=
          ENNReal.tsum_le_tsum (g := fun m : LatticeMode => ENNReal.ofReal (Cm * ‖u m‖))
            fun m => by
              by_cases hm : m = 0
              · subst hm
                exact lintegral_piCell_zero_normInv_le u j
              · exact hcell hm
      _ = ENNReal.ofReal (∑' m : LatticeMode, Cm * ‖u m‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg Cm_nonneg (norm_nonneg _))
            hsumm).symm
      _ = ENNReal.ofReal (Cm * ‖u‖) := by rw [tsum_mul_left, tsum_norm_u u]

/-! ### Space-side integrability -/

theorem integrable_norm_latticeExtensionSpaceCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun x : Space => ‖latticeExtensionSpace u x j‖) volume :=
  ⟨(measurable_latticeExtensionSpaceCoord u j).norm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all volume fun _ => norm_nonneg _)).mpr
      (lt_of_le_of_lt (lintegral_norm_latticeExtensionSpaceCoord_le u j)
        ENNReal.ofReal_lt_top)⟩

theorem integrable_normE_latticeExtensionSpaceCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun x : Space => normE x * ‖latticeExtensionSpace u x j‖) volume :=
  ⟨(measurable_normE.mul (measurable_latticeExtensionSpaceCoord u j).norm).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all volume fun x =>
        mul_nonneg (normE_nonneg x) (norm_nonneg _))).mpr
      (lt_of_le_of_lt (lintegral_normE_latticeExtensionSpaceCoord_le u j)
        ENNReal.ofReal_lt_top)⟩

theorem integrable_normInv_latticeExtensionSpaceCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun x : Space => (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖) volume :=
  ⟨aestm_normE_inv.mul (measurable_latticeExtensionSpaceCoord u j).norm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all volume fun x =>
        mul_nonneg (inv_nonneg.mpr (normE_nonneg x)) (norm_nonneg _))).mpr
      (lt_of_le_of_lt (lintegral_normInv_latticeExtensionSpaceCoord_le u j)
        ENNReal.ofReal_lt_top)⟩

/-! ### ES-side integrability (the A-carrier) -/

theorem integrable_norm_latticeExtensionCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun ξ : ES => ‖latticeExtension u ξ j‖) := by
  have hcomp : (fun ξ : ES => ‖latticeExtension u ξ j‖) ∘ (WithLp.toLp 2) =
      fun x : Space => ‖latticeExtensionSpace u x j‖ := by
    funext x
    show ‖latticeExtension u (WithLp.toLp 2 x) j‖ = ‖latticeExtensionSpace u x j‖
    rw [latticeExtension_toLp]
  refine ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mp ?_
  rw [hcomp]
  exact integrable_norm_latticeExtensionSpaceCoord u j

theorem integrable_normE_latticeExtensionCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖latticeExtension u ξ j‖) := by
  have hcomp : (fun ξ : ES => ‖ξ‖ * ‖latticeExtension u ξ j‖) ∘ (WithLp.toLp 2) =
      fun x : Space => normE x * ‖latticeExtensionSpace u x j‖ := by
    funext x
    show ‖WithLp.toLp 2 x‖ * ‖latticeExtension u (WithLp.toLp 2 x) j‖ =
      ‖WithLp.toLp 2 x‖ * ‖latticeExtensionSpace u x j‖
    rw [latticeExtension_toLp]
  refine ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mp ?_
  rw [hcomp]
  exact integrable_normE_latticeExtensionSpaceCoord u j

theorem integrable_normInv_latticeExtensionCoord (u : WeightedLatticeBanach) (j : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖latticeExtension u ξ j‖) := by
  have hcomp : (fun ξ : ES => ‖ξ‖⁻¹ * ‖latticeExtension u ξ j‖) ∘ (WithLp.toLp 2) =
      fun x : Space => (normE x)⁻¹ * ‖latticeExtensionSpace u x j‖ := by
    funext x
    show ‖WithLp.toLp 2 x‖⁻¹ * ‖latticeExtension u (WithLp.toLp 2 x) j‖ =
      ‖WithLp.toLp 2 x‖⁻¹ * ‖latticeExtensionSpace u x j‖
    rw [latticeExtension_toLp]
  refine ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mp ?_
  rw [hcomp]
  exact integrable_normInv_latticeExtensionSpaceCoord u j

/-! ## Peer budget consumption -/

private theorem coordinateX0Mass_nonneg (a : ES → ComplexSpace) :
    0 ≤ coordinateX0Mass a :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

/-- The bilinear convolution-mass factorization: the total mass of the
double-sum convolution majorant of the Navier bilinear symbol factors into the
product of the two coordinate `X⁰` masses. -/
theorem sum_convolution_eq_coordinateX0Mass_mul (a b : ES → ComplexSpace)
    (ha0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖a η j‖))
    (hb0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖b η i‖)) :
    (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ) =
      coordinateX0Mass a * coordinateX0Mass b := by
  unfold coordinateX0Mass
  rw [mul_comm]
  have hinner (i : Fin 3) : Integrable (fun ξ : ES => ∑ j : Fin 3,
      convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ) :=
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_scalar_convolution _ _ (ha0 j) (hb0 i)
  calc (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ)
      _ = ∑ i : Fin 3, ∫ ξ : ES, ∑ j : Fin 3,
            convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ :=
        integral_finsetSum Finset.univ fun i _ => hinner i
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES,
            convolution (fun η : ES => ‖a η j‖) (fun η : ES => ‖b η i‖) ξ := by
        refine Finset.sum_congr rfl fun i _ =>
          integral_finsetSum Finset.univ (fun j _ =>
            integrable_scalar_convolution _ _ (ha0 j) (hb0 i))
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
            (∫ η : ES, ‖b η i‖) * (∫ η : ES, ‖a η j‖) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Eq.trans (normX0_convolution_eq (fun η : ES => ‖a η j‖)
            (fun η : ES => ‖b η i‖) (ha0 j) (hb0 i)) (mul_comm _ _)
      _ = (∑ i : Fin 3, ∫ η : ES, ‖b η i‖) * (∑ j : Fin 3, ∫ η : ES, ‖a η j‖) := by
        rw [Finset.sum_mul_sum]

/-- Successor field (F-008): the dissipation budget of the heat flow applied
to the extension. -/
theorem integral_coordinateX1Mass_heatVec_latticeExtension_le (u : WeightedLatticeBanach)
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (heatVec ν s (latticeExtension u)) ≤
      ν⁻¹ * ((3 : ℝ) * Cm * ‖u‖) := by
  refine le_trans (integral_coordinateX1Mass_heatVec_le (latticeExtension u)
      (fun i => integrable_normInv_latticeExtensionCoord u i) ν t hν ht) ?_
  exact mul_le_mul_of_nonneg_left (coordinateXm1Mass_latticeExtension_le u)
    (inv_nonneg.mpr (le_of_lt hν))

/-- Successor field (F-008): the pressure `X⁰` budget of the extension. -/
theorem integral_norm_continuousPressureFourier_latticeExtension_le
    (u : WeightedLatticeBanach) :
    ∫ ξ : ES, ‖continuousPressureFourier (latticeExtension u) ξ‖ ≤
      ((3 : ℝ) * ‖u‖) ^ 2 := by
  refine (integral_norm_continuousPressureFourier_le (latticeExtension u)
      (fun j => aestm_latticeExtensionCoord u j)
      (fun j => integrable_norm_latticeExtensionCoord u j)).trans ?_
  nlinarith [coordinateX0Mass_latticeExtension_le u,
    coordinateX0Mass_nonneg (latticeExtension u), norm_nonneg u]

/-- Successor field (F-008): the pressure `X¹` budget of the extension. -/
theorem normX1_continuousPressureFourier_latticeExtension_le (u : WeightedLatticeBanach) :
    normX1 (continuousPressureFourier (latticeExtension u)) ≤
      2 * ((3 : ℝ) * ‖u‖) * ((3 : ℝ) * C1 * ‖u‖) := by
  refine (normX1_continuousPressureFourier_le (latticeExtension u)
      (fun j => aestm_latticeExtensionCoord u j)
      (fun j => integrable_norm_latticeExtensionCoord u j)
      (fun j => integrable_normE_latticeExtensionCoord u j)).trans ?_
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (coordinateX0Mass_latticeExtension_le u)
      (by norm_num : (0 : ℝ) ≤ 2))
    (coordinateX1Mass_latticeExtension_le u)
    (Finset.sum_nonneg fun i _ => integral_nonneg fun ξ =>
      mul_nonneg (norm_nonneg ξ) (norm_nonneg _))
    (by nlinarith [norm_nonneg u])

/-- Successor field (F-008): the pressure-gradient `X⁻¹` budget of the
extension, per coordinate. -/
theorem normXm1_continuousPressureGrad_latticeExtension_le (u : WeightedLatticeBanach)
    (i : Fin 3) :
    normXm1 (fun ξ : ES => continuousPressureGrad (latticeExtension u) ξ i) ≤
      ((3 : ℝ) * ‖u‖) ^ 2 := by
  refine (normXm1_continuousPressureGrad_le (latticeExtension u) i
      (fun j => aestm_latticeExtensionCoord u j)
      (fun j => integrable_norm_latticeExtensionCoord u j)).trans ?_
  nlinarith [coordinateX0Mass_latticeExtension_le u,
    coordinateX0Mass_nonneg (latticeExtension u), norm_nonneg u]

/-- Successor field (F-008): the bilinear symbol measurability feed holds for
the extension. -/
theorem aestm_continuousNavierBilinear_latticeExtension (u v : WeightedLatticeBanach) :
    AEStronglyMeasurable (fun ξ : ES =>
      complexEuclideanPoint (continuousNavierBilinear (latticeExtension u)
        (latticeExtension v) ξ)) :=
  continuousNavierBilinear_aestronglyMeasurable (latticeExtension u) (latticeExtension v)
    (fun j => aestm_latticeExtensionCoord u j) (fun j => aestm_latticeExtensionCoord v j)
    (fun j => integrable_norm_latticeExtensionCoord u j)
    (fun j => integrable_norm_latticeExtensionCoord v j)

/-- Successor field (F-008): the bilinear symbol `X⁻¹`-weighted amplitude
budget of the extension, in the convolution-majorant form consumed by
`normXm1_continuousDuhamel_le`. -/
theorem integral_normInv_weightedAmplitude_bilinear_latticeExtension_le
    (u v : WeightedLatticeBanach) :
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierBilinear (latticeExtension u) (latticeExtension v) ξ)) ≤
      coordinateX0Mass (latticeExtension u) * coordinateX0Mass (latticeExtension v) := by
  refine le_trans (integral_mono
    (integrable_normXm1_continuousNavierBilinear (latticeExtension u) (latticeExtension v)
      (fun j => aestm_latticeExtensionCoord u j) (fun j => aestm_latticeExtensionCoord v j)
      (fun j => integrable_norm_latticeExtensionCoord u j)
      (fun j => integrable_norm_latticeExtensionCoord v j))
    (integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ =>
        integrable_scalar_convolution _ _ (integrable_norm_latticeExtensionCoord u j)
          (integrable_norm_latticeExtensionCoord v i))
    (normXm1_continuousNavierBilinear_pointwise (latticeExtension u) (latticeExtension v))) ?_
  rw [sum_convolution_eq_coordinateX0Mass_mul (latticeExtension u) (latticeExtension v)
    (fun j => integrable_norm_latticeExtensionCoord u j)
    (fun j => integrable_norm_latticeExtensionCoord v j)]

/-- Successor field (F-008): the bilinear symbol amplitude budget in
carrier-norm form. -/
theorem integral_normInv_weightedAmplitude_bilinear_latticeExtension_norm_le
    (u v : WeightedLatticeBanach) :
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierBilinear (latticeExtension u) (latticeExtension v) ξ)) ≤
      ((3 : ℝ) * ‖u‖) * ((3 : ℝ) * ‖v‖) := by
  refine (integral_normInv_weightedAmplitude_bilinear_latticeExtension_le u v).trans
    (mul_le_mul (coordinateX0Mass_latticeExtension_le u)
      (coordinateX0Mass_latticeExtension_le v)
      (coordinateX0Mass_nonneg (latticeExtension v))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ)) (norm_nonneg u)))

/-! ## Energy contract (F-008 successor field): per-coordinate `L²` budget -/

/-- The per-coordinate `L²` energy of the cell extension is bounded by the
squared carrier norm: `∫ ‖u m‖² ≤ (∑' ‖u m‖)²` transported cell by cell. -/
theorem integral_norm_sq_latticeExtensionSpaceCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ x : Space, ‖latticeExtensionSpace u x j‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hae : 0 ≤ᵐ[volume] fun x : Space => ‖latticeExtensionSpace u x j‖ ^ 2 :=
    ae_of_all volume fun x => pow_two_nonneg _
  have hs : AEStronglyMeasurable (fun x : Space => ‖latticeExtensionSpace u x j‖ ^ 2) volume := by
    refine ⟨fun x : Space => ‖latticeExtensionSpace u x j‖ * ‖latticeExtensionSpace u x j‖,
      ((measurable_latticeExtensionSpaceCoord u j).norm.mul
        (measurable_latticeExtensionSpaceCoord u j).norm).stronglyMeasurable,
      ae_of_all volume fun x => pow_two _⟩
  have hsumm : Summable (fun m : LatticeMode => ‖u‖ * ‖u m‖) :=
    (summable_norm_u u).mul_left ‖u‖
  rw [integral_eq_lintegral_of_nonneg_ae hae hs]
  calc (∫⁻ x, ENNReal.ofReal (‖latticeExtensionSpace u x j‖ ^ 2)).toReal
      ≤ (ENNReal.ofReal (‖u‖ * ‖u‖)).toReal :=
          ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top)
            (le_trans (Eq.le (lintegral_piCell_tsum _))
              (le_trans
                (ENNReal.tsum_le_tsum
                  (g := fun m : LatticeMode => ENNReal.ofReal (‖u‖ * ‖u m‖))
                  fun m =>
                    lintegral_piCell_le_const m
                      (fun x => ENNReal.ofReal (‖latticeExtensionSpace u x j‖ ^ 2))
                      (ENNReal.ofReal (‖u‖ * ‖u m‖))
                      (fun x hx => ENNReal.ofReal_le_ofReal
                        (by
                          have hc : ‖latticeExtensionSpace u x j‖ ≤ ‖u m‖ := by
                            rw [latticeExtensionSpace_apply, (mem_piCell m x).mp hx]
                            exact coeff_coord_le u m j
                          calc ‖latticeExtensionSpace u x j‖ ^ 2
                              ≤ ‖u m‖ ^ 2 := by
                                rw [sq, sq]
                                exact mul_le_mul hc hc (norm_nonneg _) (norm_nonneg _)
                            _ ≤ ‖u‖ * ‖u m‖ := by
                                rw [sq]
                                exact mul_le_mul (norm_weightedLattice_eval_le u m)
                                  (le_refl _) (norm_nonneg _) (norm_nonneg _))))
                (by
                  rw [← ENNReal.ofReal_tsum_of_nonneg
                    (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsumm,
                    tsum_mul_left, tsum_norm_u u])))
    _ = ‖u‖ ^ 2 := by
        rw [ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _)), pow_two]

/-- Successor field (F-008): the per-coordinate `L²` datum energy of the
extension on the `A` carrier. -/
theorem integral_norm_sq_latticeExtensionCoord_le (u : WeightedLatticeBanach) (j : Fin 3) :
    ∫ ξ : ES, ‖latticeExtension u ξ j‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  calc (∫ ξ : ES, ‖latticeExtension u ξ j‖ ^ 2)
      = ∫ x : Space, ‖latticeExtensionSpace u x j‖ ^ 2 := by
          refine ((integral_congr_ae (ae_of_all volume fun ξ : ES => rfl)).trans
            (integral_spaceProj (fun x : Space => ‖latticeExtensionSpace u x j‖ ^ 2)))
    _ ≤ ‖u‖ ^ 2 := integral_norm_sq_latticeExtensionSpaceCoord_le u j

/-! ## Honest boundary: the mild self-map time obligation -/

/-- OPEN obligation, declared and never assumed: the spacetime `X¹` feed of
the mild assembly on the transported datum — integrability in time of
`t ↦ coordinateX1Mass (heatVec ν t (latticeExtension u))` on every finite
interval, the input shape consumed by the peer time leaves (`hmX1`,
`ContinuousLeiLinMildAssemblyLeaves`, and via
`normXm1_continuousDuhamel_le` the Duhamel assembly). The spatial budgets
this obligation needs are proved in this file (`X⁰`, `X¹`, `X⁻¹` masses,
heat, pressure, pressure-gradient and bilinear convolution majorants); the
remaining content is the time-direction integrability of the heat flow of
the extension, which is peer mild-assembly machinery, not a defect of this
transport. Nothing in this file depends on this declaration. -/
def MildSelfMapTransport (u : WeightedLatticeBanach) : Prop :=
  ∀ (ν : ℝ) (_hν : 0 < ν) (T : ℝ),
    Integrable (fun t : ℝ => coordinateX1Mass (heatVec ν t (latticeExtension u)))
      (volume.restrict (Set.Icc (0 : ℝ) T))

end Navier.Transfer.LatticeExtensionTransport
