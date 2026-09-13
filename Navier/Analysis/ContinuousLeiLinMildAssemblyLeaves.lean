import Navier.Analysis.ContinuousLeiLinMildFixedPoint
import Navier.Analysis.ContinuousLeiLinActualPolarization
import Navier.Analysis.ComplexLerayNorm
import Navier.Analysis.FourierMajorant
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mild assembly leaves for general (quotient-represented) box elements

This module constructs the `MildAssemblyLeaves` record for *every* element of
the actual linked box, i.e. for general `Lᵖ`-completion-represented carriers.
The single hard input is joint measurability: a spacetime slot element
`L¹_t(L¹_ξ)` admits a jointly strongly measurable version whose time sections
represent the slot almost everywhere (`exists_stronglyMeasurable_jointVersion`).
Every joint-source leaf then consumes this one primitive through a shared
joint-source measurability lemma, and the remaining leaves are assembled from
the existing sorry-free machinery.

Assumptions made here: none beyond what the file's imports already carry.
Nothing in this module is fixed-point-shaped or conclusion-shaped.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false -- haveI (not have) is required to register the SFinite instances below
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set ENNReal Topology Filter
open scoped BigOperators Convolution NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.FourierMajorant

namespace Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves

/-! ## S0: measure transfer helpers -/

theorem eventually_of_eventually_of_ac {α : Type*} {_ : MeasurableSpace α}
    {μ ν : Measure α} {p : α → Prop} (hac : μ ≪ ν) (h : ∀ᵐ x ∂ν, p x) :
    ∀ᵐ x ∂μ, p x :=
  ae_iff.mpr (hac (ae_iff.mp h))

/-! ## S1: the joint measurable version of a spacetime slot

The primitive: every element of the nested slot `L¹(μt; L¹(μf))` has a version
`u : ES × ℝ → FourierCoordinateL1` which is jointly strongly measurable and
whose time sections `(fun ξ => u (ξ, t))` represent the slot `μt`-a.e.
The proof internally works on the product measure `μt.prod μf` over `ℝ × ES`
so Tonelli reads t-outer without a swap lemma, approximates the slot by
`ℝ`-simple functions into the spatial `L¹`, lifts each simple function to a
joint one using fixed strongly measurable covers of the spatial classes,
completes in `L¹(μt.prod μf)`, and identifies the limit's sections by a
Borel-Cantelli argument on two measurable error profiles.
-/

/-- A fixed strongly measurable cover of the canonical representative of a
spatial `L¹` class. -/
noncomputable def spatialCover (μf : Measure ES)
    (c : Lp FourierCoordinateL1 1 μf) : ES → FourierCoordinateL1 :=
  (Lp.aestronglyMeasurable c).mk ⇑c

private theorem spatialCover_stronglyMeasurable (μf : Measure ES)
    (c : Lp FourierCoordinateL1 1 μf) :
    StronglyMeasurable (spatialCover μf c) :=
  (Lp.aestronglyMeasurable c).stronglyMeasurable_mk

private theorem spatialCover_ae_eq (μf : Measure ES)
    (c : Lp FourierCoordinateL1 1 μf) :
    spatialCover μf c =ᵐ[μf] ⇑c := ((Lp.aestronglyMeasurable c).ae_eq_mk).symm

/-- **The joint version primitive.**  Every element of the nested spacetime
slot `L¹_t(L¹_ξ)` admits a jointly strongly measurable version whose time
sections represent the slot almost everywhere in time.  This is the single
primitive from which every joint measurability leaf is derived; no leaf
rebuilds it. -/
theorem exists_stronglyMeasurable_jointVersion (μf : Measure ES) (μt : Measure ℝ)
    (hμf : SFinite μf) (_hμt : SFinite μt)
    (F : Lp (Lp FourierCoordinateL1 1 μf) 1 μt) :
    ∃ u : ES × ℝ → FourierCoordinateL1,
      StronglyMeasurable u ∧
        ∀ᵐ t ∂μt, (fun ξ : ES => u (ξ, t)) =ᵐ[μf] (fun ξ : ES => ⇑(F t) ξ) := by
  haveI : SFinite μf := hμf
  haveI : SFinite μt := _hμt
  set Sp := Lp FourierCoordinateL1 1 μf with hSp
  set μp : Measure (ℝ × ES) := μt.prod μf with hμp
  -- Approximation of the time-slot direction by spatial-valued simple functions.
  have hF : MemLp (F : ℝ → Sp) 1 μt := Lp.memLp F
  have happrox (n : ℕ) : ∃ g : SimpleFunc ℝ Sp,
      eLpNorm ((F : ℝ → Sp) - ⇑g) 1 μt < ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹) ∧ MemLp ⇑g 1 μt :=
    (hF).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top
      (ε := ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹))
      (ne_of_lt (ENNReal.ofReal_pos.mpr (by positivity))).symm
  choose s hsn hsM using happrox
  --  ### Joint lift of the approximating simple functions
  let js : ℕ → (ℝ × ES → FourierCoordinateL1) := fun n =>
    ∑ c ∈ (s n).range,
      Set.indicator (Prod.fst ⁻¹' (⇑(s n) ⁻¹' {c}))
        (spatialCover μf c ∘ Prod.snd)
  have hjs_point (n : ℕ) (t : ℝ) (ξ : ES) :
      js n (t, ξ) = spatialCover μf (s n t) ξ := by
    classical
    have hmem : s n t ∈ (s n).range :=
      (SimpleFunc.mem_range (f := s n)).mpr ⟨t, rfl⟩
    have hin : (t, ξ) ∈ Prod.fst ⁻¹' (⇑(s n) ⁻¹' {s n t}) := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
    show (∑ c ∈ (s n).range,
        Set.indicator (Prod.fst ⁻¹' (⇑(s n) ⁻¹' {c}))
          (spatialCover μf c ∘ Prod.snd)) (t, ξ) = spatialCover μf (s n t) ξ
    rw [Finset.sum_apply]
    refine (Finset.sum_eq_single (s n t) (fun c _ hne => ?_) (fun h => absurd hmem h)).trans ?_
    · have hn : (t, ξ) ∉ Prod.fst ⁻¹' (⇑(s n) ⁻¹' {c}) := by
        intro h
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
        exact hne h.symm
      refine (Set.indicator_apply (M := FourierCoordinateL1) (Prod.fst ⁻¹' (⇑(s n) ⁻¹' {c}))
          (spatialCover μf c ∘ Prod.snd) (t, ξ)).trans ?_
      exact ite_eq_right_iff.mpr fun hc => False.elim (hn hc)
    · exact Set.indicator_of_mem hin (spatialCover μf (s n t) ∘ Prod.snd)
  have hjs_aes (n : ℕ) : AEStronglyMeasurable (js n) μp :=
    Finset.aestronglyMeasurable_sum (s n).range fun c _ =>
      AEStronglyMeasurable.indicator
        ((spatialCover_stronglyMeasurable μf c).comp_measurable
            continuous_snd.measurable).aestronglyMeasurable
        (MeasurableSet.preimage ((s n).measurableSet_fiber c) measurable_fst)
  have hjs_sec (n : ℕ) (t : ℝ) : (fun ξ : ES => js n (t, ξ)) =ᵐ[μf] ⇑(s n t) := by
    filter_upwards [spatialCover_ae_eq μf (s n t)] with ξ hξ
    simpa [hjs_point n t] using hξ
  have hsec_norm (n : ℕ) (t : ℝ) :
      ∫⁻ ξ : ES, ‖js n (t, ξ)‖ₑ ∂μf = ‖⇑(s n) t‖ₑ := by
    rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae (hjs_sec n t), Lp.enorm_def]
  have hsec_diff (m n : ℕ) (t : ℝ) :
      ∫⁻ ξ : ES, ‖js m (t, ξ) - js n (t, ξ)‖ₑ ∂μf = ‖⇑(s m) t - ⇑(s n) t‖ₑ := by
    have h : (fun ξ : ES => js m (t, ξ) - js n (t, ξ)) =ᵐ[μf]
        ⇑(⇑(s m) t - ⇑(s n) t) := by
      filter_upwards [hjs_sec m t, hjs_sec n t, Lp.coeFn_sub (s m t) (s n t)] with ξ h1 h2 h3
      rw [h1, h2, h3, ← Pi.sub_apply]
    rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae h, Lp.enorm_def]
  --  ### The joint lift preserves the slot norm (t-outer Tonelli, no swap).
  have hjs_eLp (n : ℕ) : eLpNorm (js n) 1 μp = eLpNorm (⇑(s n)) 1 μt := by
    have h1 : AEMeasurable (fun p : ℝ × ES => ‖js n p‖ₑ) μp := by
      have h2 := (hjs_aes n).aemeasurable
      fun_prop
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm, hμp,
      lintegral_prod (f := fun p : ℝ × ES => ‖js n p‖ₑ) h1]
    exact lintegral_congr fun t => hsec_norm n t
  --  ### Completeness in the joint product space.
  have hjs_mem (n : ℕ) : MemLp (js n) 1 μp :=
    ⟨hjs_aes n, by rw [hjs_eLp]; exact (hsM n).2⟩
  let hL : ℕ → Lp FourierCoordinateL1 1 μp := fun n => (hjs_mem n).toLp (js n)
  have hL_coe (n : ℕ) : ⇑(hL n) =ᵐ[μp] js n := MemLp.coeFn_toLp (hjs_mem n)
  -- pointwise enorm triangle on the spatial slot (ENNReal norm of an L¹ class)
  have hpointwise (x y : Sp) : ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
    have exy : ‖x + y‖ₑ = ENNReal.ofReal ‖x + y‖ := by simp
    have ex : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by simp
    have ey : ‖y‖ₑ = ENNReal.ofReal ‖y‖ := by simp
    rw [exy, ex, ey, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  have hc : CauchySeq hL := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨i, hi⟩ := exists_nat_gt ((2 : ℝ) / ε)
    refine ⟨i, fun j hj => fun n hn => ?_⟩
    have hdiff : ⇑(hL j) - ⇑(hL n) =ᵐ[μp] fun p : ℝ × ES => js j p - js n p := by
      filter_upwards [hL_coe j, hL_coe n] with p h1 h2
      show ⇑(hL j) p - ⇑(hL n) p = js j p - js n p
      rw [h1, h2]
    have hdist : dist (hL j) (hL n) =
        (eLpNorm (fun p : ℝ × ES => js j p - js n p) 1 μp).toReal := by
      rw [Lp.dist_def, eLpNorm_congr_ae hdiff]
    have hprod : eLpNorm (fun p : ℝ × ES => js j p - js n p) 1 μp =
        eLpNorm (fun t : ℝ => ⇑(s j) t - ⇑(s n) t) 1 μt := by
      have h1 : AEMeasurable (fun p : ℝ × ES => ‖js j p - js n p‖ₑ) μp := by
        have h2 := (hjs_aes j).sub (hjs_aes n)
        fun_prop
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm, hμp,
        lintegral_prod (f := fun p : ℝ × ES => ‖js j p - js n p‖ₑ) h1]
      exact lintegral_congr fun t => hsec_diff j n t
    have hjt : eLpNorm (fun t : ℝ => ⇑(s j) t - ⇑F t) 1 μt <
        ENNReal.ofReal ((↑j + 1 : ℝ)⁻¹) := by
      rw [show (fun t : ℝ => ⇑(s j) t - ⇑F t) = -(fun t : ℝ => ⇑F t - ⇑(s j) t) from by
        funext t; simp only [Pi.neg_apply, neg_sub], eLpNorm_neg]
      exact hsn j
    have hnt : eLpNorm (fun t : ℝ => ⇑F t - ⇑(s n) t) 1 μt <
        ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹) := hsn n
    have hslot : eLpNorm (fun t : ℝ => ⇑(s j) t - ⇑(s n) t) 1 μt <
        ENNReal.ofReal ((↑j + 1 : ℝ)⁻¹) + ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹) := by
      have haj : AEStronglyMeasurable (fun t : ℝ => ⇑(s j) t - ⇑F t) μt :=
        (hsM j).1.sub (Lp.aestronglyMeasurable F)
      have hbi : AEStronglyMeasurable (fun t : ℝ => ⇑F t - ⇑(s n) t) μt :=
        (Lp.aestronglyMeasurable F).sub (hsM n).1
      have hdeq : (fun t : ℝ => ⇑(s j) t - ⇑(s n) t) =
          (fun t : ℝ => ⇑(s j) t - ⇑F t) + (fun t : ℝ => ⇑F t - ⇑(s n) t) := by
        funext t
        show ⇑(s j) t - ⇑(s n) t = (⇑(s j) t - ⇑F t) + (⇑F t - ⇑(s n) t)
        abel
      rw [hdeq]
      refine (eLpNorm_add_le haj hbi le_rfl).trans_lt ?_
      exact ENNReal.add_lt_add hjt hnt
    have hsum : ENNReal.ofReal ((↑j + 1 : ℝ)⁻¹) + ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹) ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨by finiteness, by finiteness⟩
    have hne : eLpNorm (fun p : ℝ × ES => js j p - js n p) 1 μp ≠ ∞ := by
      rw [hprod]
      exact ne_of_lt (hslot.trans (lt_top_iff_ne_top.mpr hsum))
    have htoReal :
        (eLpNorm (fun p : ℝ × ES => js j p - js n p) 1 μp).toReal ≤
          (ENNReal.ofReal ((↑j + 1 : ℝ)⁻¹) + ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹)).toReal :=
      (ENNReal.toReal_le_toReal hne hsum).mpr (hprod.trans_le hslot.le)
    have hinv : (ENNReal.ofReal ((↑j + 1 : ℝ)⁻¹) + ENNReal.ofReal ((↑n + 1 : ℝ)⁻¹)).toReal
        = ((j : ℝ) + 1)⁻¹ + ((n : ℝ) + 1)⁻¹ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.toReal_ofReal (by positivity)
    have hlt : ((j : ℝ) + 1)⁻¹ + ((n : ℝ) + 1)⁻¹ < ε := by
      have h2i : (2 : ℝ) / ε < (i : ℝ) := by exact_mod_cast hi
      have hy : 0 < (2 : ℝ) / ε := by positivity
      have hi1 : 0 < (i : ℝ) + 1 := by positivity
      have hj1p : 0 < (j : ℝ) + 1 := by positivity
      have hn1p : 0 < (n : ℝ) + 1 := by positivity
      have hinv_i : ((i : ℝ) + 1)⁻¹ < ε / 2 := by
        rw [show ε / 2 = ((2 : ℝ) / ε)⁻¹ by field_simp]
        exact (inv_lt_inv₀ hi1 hy).mpr (by linarith)
      have hinv_j : ((j : ℝ) + 1)⁻¹ ≤ ((i : ℝ) + 1)⁻¹ :=
        (inv_le_inv₀ hj1p hi1).mpr (by exact_mod_cast Nat.succ_le_succ hj)
      have hinv_n : ((n : ℝ) + 1)⁻¹ ≤ ((i : ℝ) + 1)⁻¹ :=
        (inv_le_inv₀ hn1p hi1).mpr (by exact_mod_cast Nat.succ_le_succ hn)
      linarith
    rw [hdist]
    refine htoReal.trans_lt ?_
    rw [hinv]
    exact hlt
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete hc
  --  ### The limit's own strongly measurable version and its error profile.
  let u' : ℝ × ES → FourierCoordinateL1 := (Lp.aestronglyMeasurable U).mk ⇑U
  have hu'_SM : StronglyMeasurable u' :=
    (Lp.aestronglyMeasurable U).stronglyMeasurable_mk
  have hu'_coe : ⇑U =ᵐ[μp] u' := (Lp.aestronglyMeasurable U).ae_eq_mk
  have hUe (n : ℕ) : ⇑(U - hL n) =ᵐ[μp] fun p => u' p - js n p := by
    filter_upwards [Lp.coeFn_sub U (hL n), hu'_coe, hL_coe n] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  set δ : ℕ → ℝ → ENNReal := fun n t => ∫⁻ ξ : ES, ‖u' (t, ξ) - js n (t, ξ)‖ₑ ∂μf
  have hδ_int (n : ℕ) : ∫⁻ t : ℝ, δ n t ∂μt = ‖U - hL n‖ₑ := by
    have h1 : AEMeasurable (fun p : ℝ × ES => ‖u' p - js n p‖ₑ) μp := by
      have h2 : ⇑U =ᵐ[μp] u' := hu'_coe
      have h3 := Lp.aestronglyMeasurable U
      have h4 := hjs_aes n
      fun_prop
    calc ∫⁻ t : ℝ, δ n t ∂μt
        = ∫⁻ p : ℝ × ES, ‖u' p - js n p‖ₑ ∂μp := by
          rw [hμp, lintegral_prod (f := fun p : ℝ × ES => ‖u' p - js n p‖ₑ) h1]
      _ = eLpNorm (fun p : ℝ × ES => u' p - js n p) 1 μp :=
          (eLpNorm_one_eq_lintegral_enorm).symm
      _ = ‖U - hL n‖ₑ := by rw [← eLpNorm_congr_ae (hUe n), ← Lp.enorm_def]
  have hδ_meas (n : ℕ) : AEMeasurable (δ n) μt := by
    -- sectionwise integrand is a.e. measurable; push through the product
    have h1 : AEMeasurable (fun p : ℝ × ES => ‖u' p - js n p‖ₑ) μp := by
      have h3 := Lp.aestronglyMeasurable U
      have h4 := hjs_aes n
      fun_prop
    have h2 :
        AEMeasurable
          (Function.uncurry (fun (t : ℝ) (ξ : ES) => ‖u' (t, ξ) - js n (t, ξ)‖ₑ)) μp := h1
    have := h2.lintegral_prod_right (μ := μt) (ν := μf)
    simpa [δ, hμp] using this
  --  ### Borel-Cantelli summability bound for the geometric envelope.
  have hgeom : (∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)) ≠ ∞ := by
    have hle : ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) ≤
        ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k := by
      refine ENNReal.tsum_le_tsum (fun k => pow_le_pow_of_le_one (by positivity)
        (by norm_num) (Nat.le_add_right k 1))
    rw [ENNReal.tsum_geometric_two] at hle
    exact (lt_of_le_of_lt hle (by norm_num)).ne
  --  ### Select the subsequence with geometric envelope.
  let r : ℕ → ℝ := fun k => ((2 : ℝ) ^ (k + 1))⁻¹
  have hrpos : ∀ k, 0 < r k := fun k => by
    simp only [r]; positivity
  have hstep : ∀ (k m : ℕ), ∃ n : ℕ, m ≤ n ∧ ((2 : ℝ) ^ (k + 1) : ℝ) ≤ (n : ℝ) ∧
      ‖U - hL n‖ < r k := by
    intro k m
    have hconv : ∃ N1 : ℕ, ∀ n ≥ N1, ‖U - hL n‖ < r k := by
      rw [Metric.tendsto_atTop] at hU
      obtain ⟨N1, hN1⟩ := hU (r k) (hrpos k)
      exact ⟨N1, fun n hn => by
        rw [← (dist_comm (hL n) U).trans (dist_eq_norm U (hL n))]
        exact hN1 n hn⟩
    obtain ⟨N1, hN1⟩ := hconv
    obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n ≥ N2, m ≤ n ∧ ((2 : ℝ) ^ (k + 1) : ℝ) ≤ (n : ℝ) :=
      ⟨max m ((2 : ℕ) ^ (k + 1)), fun n hn =>
        ⟨Nat.le_trans (Nat.le_max_left _ _) hn, by
          exact_mod_cast Nat.le_trans (Nat.le_max_right _ _) hn⟩⟩
    exact ⟨max N1 N2, (hN2 _ (Nat.le_max_right _ _)).1, (hN2 _ (Nat.le_max_right _ _)).2,
      hN1 _ (Nat.le_max_left _ _)⟩
  choose nsub hnsub using fun k => hstep k 0
  --  ### The δ profile is summable in `k` along the subsequence.
  have hr_env (k : ℕ) : ENNReal.ofReal (r k) = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
    show ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹) = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)
    rw [show ((2 : ℝ) ^ (k + 1))⁻¹ = ((2 : ℝ)⁻¹) ^ (k + 1) by rw [← inv_pow]]
    rw [ENNReal.ofReal_pow (by positivity)]
    simp
  --  ### The θ profile: time-slot approximation error, measurable via
  --  ### `AEStronglyMeasurable.enorm` (no `MeasurableSpace (Lp)` instance is
  --  ### ever produced or needed).
  set θ : ℕ → ℝ → ENNReal := fun n t => ‖⇑F t - ⇑(s n) t‖ₑ
  have hθ_meas (n : ℕ) : AEMeasurable (θ n) μt := by
    have h : AEStronglyMeasurable (fun t : ℝ => ⇑F t - ⇑(s n) t) μt :=
      (Lp.aestronglyMeasurable F).sub (hsM n).1
    exact h.enorm
  have hθ_int (n : ℕ) : ∫⁻ t : ℝ, θ n t ∂μt = eLpNorm (⇑F - ⇑(s n)) 1 μt := by
    rw [show θ n = fun t : ℝ => ‖(⇑F - ⇑(s n)) t‖ₑ from by
      funext t
      show ‖⇑F t - ⇑(s n) t‖ₑ = ‖(⇑F - ⇑(s n)) t‖ₑ
      rw [Pi.sub_apply]]
    exact (eLpNorm_one_eq_lintegral_enorm (f := ⇑F - ⇑(s n))).symm
  have hk_theta (k : ℕ) : ∫⁻ t : ℝ, θ (nsub k) t ∂μt ≤ ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
    rw [hθ_int]
    have hle : ((nsub k : ℝ) + 1)⁻¹ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by
        have h2 := (hnsub k).2.1
        linarith)
    exact (((hsn (nsub k)).trans_le (ENNReal.ofReal_le_ofReal hle)).trans_eq (hr_env k)).le
  have hk_delta (k : ℕ) : ∫⁻ t : ℝ, δ (nsub k) t ∂μt ≤ ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
    rw [hδ_int]
    refine ((calc ‖U - hL (nsub k)‖ₑ
          = ENNReal.ofReal ‖U - hL (nsub k)‖ := by simp
        _ < ENNReal.ofReal (r k) :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr (hnsub k).2.2
        _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := hr_env k).le)
  --  ### The combined profile θ + δ is integrable, hence finite a.e.; along the
  --  ### subsequence both profiles converge to 0 pointwise a.e. (Borel-Cantelli).
  have hγ_meas (k : ℕ) : AEMeasurable (fun t : ℝ => θ (nsub k) t + δ (nsub k) t) μt := by
    fun_prop
  have hΦ_meas : AEMeasurable (fun t : ℝ => ∑' k : ℕ, (θ (nsub k) t + δ (nsub k) t)) μt := by
    fun_prop
  have htend : ∫⁻ t : ℝ, ∑' k : ℕ, (θ (nsub k) t + δ (nsub k) t) ∂μt ≤
      (∑' k : ℕ, ∫⁻ t : ℝ, θ (nsub k) t ∂μt) + ∑' k : ℕ, ∫⁻ t : ℝ, δ (nsub k) t ∂μt := by
    have h1 : ∫⁻ t : ℝ, ∑' k : ℕ, (θ (nsub k) t + δ (nsub k) t) ∂μt =
        ∑' k : ℕ, ∫⁻ t : ℝ, (θ (nsub k) t + δ (nsub k) t) ∂μt :=
      lintegral_tsum hγ_meas
    rw [h1]
    calc ∑' k : ℕ, ∫⁻ t : ℝ, (θ (nsub k) t + δ (nsub k) t) ∂μt
        ≤ ∑' k : ℕ, ((∫⁻ t : ℝ, θ (nsub k) t ∂μt) + ∫⁻ t : ℝ, δ (nsub k) t ∂μt) :=
          ENNReal.tsum_le_tsum fun k => by
            rw [lintegral_add_left' (hθ_meas (nsub k))]
      _ = ∑' k : ℕ, ∫⁻ t : ℝ, θ (nsub k) t ∂μt + ∑' k : ℕ, ∫⁻ t : ℝ, δ (nsub k) t ∂μt :=
          ENNReal.tsum_add
  have hsum_theta : (∑' k : ℕ, ∫⁻ t : ℝ, θ (nsub k) t ∂μt) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hk_theta) (lt_top_iff_ne_top.mpr hgeom))
  have hsum_delta : (∑' k : ℕ, ∫⁻ t : ℝ, δ (nsub k) t ∂μt) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hk_delta) (lt_top_iff_ne_top.mpr hgeom))
  have hae : ∀ᵐ t ∂μt, ∑' k : ℕ, (θ (nsub k) t + δ (nsub k) t) < ∞ :=
    ae_lt_top' hΦ_meas
      (ne_of_lt (lt_of_le_of_lt htend
        (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hsum_theta, hsum_delta⟩))))
  --  ### Pointwise domination: for every time t and every n the spatial
  --  ### discrepancy between the slot section and the limit section is bounded
  --  ### by the two error profiles θ n t + δ n t.
  have hsec_prod (t : ℝ) : Measurable (fun ξ : ES => (t, ξ)) := by
    show Measurable (fun x : ES => (t, x))
    exact Measurable.prod measurable_const measurable_id
  have hu'_sec (t : ℝ) : AEStronglyMeasurable (fun ξ : ES => u' (t, ξ)) μf :=
    (hu'_SM.comp_measurable (hsec_prod t)).aestronglyMeasurable
  have hle_main (t : ℝ) (n : ℕ) :
      eLpNorm (fun ξ : ES => ⇑(F t) ξ - u' (t, ξ)) 1 μf ≤ θ n t + δ n t := by
    have ha1 : AEStronglyMeasurable (fun ξ : ES => ⇑(F t) ξ - ⇑(s n) t ξ) μf :=
      (Lp.aestronglyMeasurable (F t)).sub (Lp.aestronglyMeasurable (⇑(s n) t))
    have ha2 : AEStronglyMeasurable (fun ξ : ES => ⇑(s n) t ξ - u' (t, ξ)) μf :=
      (Lp.aestronglyMeasurable (⇑(s n) t)).sub (hu'_sec t)
    have hdeq : (fun ξ : ES => ⇑(F t) ξ - u' (t, ξ)) =
        (fun ξ : ES => ⇑(F t) ξ - ⇑(s n) t ξ) + (fun ξ : ES => ⇑(s n) t ξ - u' (t, ξ)) := by
      funext ξ
      show ⇑(F t) ξ - u' (t, ξ) = (⇑(F t) ξ - ⇑(s n) t ξ) + (⇑(s n) t ξ - u' (t, ξ))
      abel
    have e1 : eLpNorm (fun ξ : ES => ⇑(F t) ξ - ⇑(s n) t ξ) 1 μf = ‖⇑F t - ⇑(s n) t‖ₑ :=
      ((eLpNorm_congr_ae ((Lp.coeFn_sub (F t) (⇑(s n) t)).symm)).trans
        ((Lp.enorm_def (f := ⇑F t - ⇑(s n) t)).symm))
    have e2 : eLpNorm (fun ξ : ES => ⇑(s n) t ξ - u' (t, ξ)) 1 μf = δ n t := by
      have hw : (fun ξ : ES => ⇑(s n) t ξ - u' (t, ξ)) =ᵐ[μf]
          (fun ξ : ES => js n (t, ξ) - u' (t, ξ)) := by
        filter_upwards [hjs_sec n t] with ξ h
        show ⇑(s n) t ξ - u' (t, ξ) = js n (t, ξ) - u' (t, ξ)
        rw [← h]
      have hneg : (fun ξ : ES => js n (t, ξ) - u' (t, ξ)) =
          -fun ξ : ES => u' (t, ξ) - js n (t, ξ) := by
        funext ξ
        show js n (t, ξ) - u' (t, ξ) = -(u' (t, ξ) - js n (t, ξ))
        rw [neg_sub]
      rw [eLpNorm_congr_ae hw, hneg, eLpNorm_neg]
      exact eLpNorm_one_eq_lintegral_enorm
    rw [hdeq]
    exact (eLpNorm_add_le ha1 ha2 le_rfl).trans (add_le_add e1.le e2.le)
  --  ### Squeeze: the discrepancy is ≥ 0 and tends to 0 along the subsequence,
  --  ### hence 0 a.e.; `eLpNorm_eq_zero_iff` converts this into the section
  --  ### almost-everywhere equality, and the coordinate swap transports it.
  have heq_zero :
      ∀ᵐ t ∂μt, eLpNorm (fun ξ : ES => ⇑(F t) ξ - u' (t, ξ)) 1 μf = 0 := by
    filter_upwards [hae] with t ht
    have hθ0 : Tendsto (fun k : ℕ => θ (nsub k) t) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_of_lt
        (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => le_self_add) ht))
    have hδ0 : Tendsto (fun k : ℕ => δ (nsub k) t) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_of_lt
        (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => le_add_of_nonneg_left zero_le) ht))
    have h0sum : Tendsto (fun k : ℕ => θ (nsub k) t + δ (nsub k) t) atTop (𝓝 0) := by
      simpa using hθ0.add hδ0
    exact le_antisymm
      (ge_of_tendsto h0sum (Filter.Eventually.of_forall fun k => hle_main t (nsub k)))
      zero_le
  have hfinal : ∀ᵐ t ∂μt, (fun ξ : ES => u' (t, ξ)) =ᵐ[μf] (fun ξ : ES => ⇑(F t) ξ) := by
    filter_upwards [heq_zero] with t ht
    have h0 : (fun ξ : ES => ⇑(F t) ξ - u' (t, ξ)) =ᵐ[μf] 0 :=
      (eLpNorm_eq_zero_iff (f := fun ξ : ES => ⇑(F t) ξ - u' (t, ξ)) (p := 1) (μ := μf)
        ((Lp.aestronglyMeasurable (F t)).sub (hu'_sec t))
        (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp ht
    filter_upwards [h0] with ξ h
    exact (sub_eq_zero.mp h).symm
  refine ⟨fun p : ES × ℝ => u' (p.2, p.1), ?_, ?_⟩
  · exact hu'_SM.comp_measurable measurable_swap
  · filter_upwards [hfinal] with t ht
    simpa using ht
/-! ## S2: joint measurability of the genuine Navier sources of all box elements

The three joint-source leaves of the assembly record (`hjointDiag`,
`hjointL`, `hjointR`) are constructed here for *general*
quotient-represented box elements.  Every one of them consumes the same
joint-proxy transport lemma, whose proof is the coordinate-level lemma plus
an a.e. transfer along the time sections of the S1 joint version; the
diagonal and both ordered mixed instances therefore share a single
measurability argument.  Nothing here is fixed-point-shaped: no leaf
assumes any mild image, moment budget, or self-map property.
-/

/-- Strongly-measurable analogue of the RecentTailInputs joint-continuity
convolution lemma: the spacetime convolution of two coordinate trajectories
is a.e. strongly measurable when each is strongly measurable on `ES × ℝ`
through the `(ξ, t)` slot. -/
theorem aestronglyMeasurable_convolution_pair {μ : Measure (ES × ℝ)}
    (f g : ℝ → ES → ℂ)
    (hf : StronglyMeasurable (fun p : ES × ℝ => f p.2 p.1))
    (hg : StronglyMeasurable (fun p : ES × ℝ => g p.2 p.1)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      ((fun η : ES => f p.2 η) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => g p.2 η)) p.1) μ := by
  have hInt : StronglyMeasurable (fun q : (ES × ℝ) × ES =>
      f q.1.2 q.2 * g q.1.2 (q.1.1 - q.2)) := by
    have hmapf : Continuous (fun q : (ES × ℝ) × ES => (q.2, q.1.2)) :=
      continuous_snd.prodMk (continuous_snd.comp continuous_fst)
    have hmapg : Continuous (fun q : (ES × ℝ) × ES =>
        (q.1.1 - q.2, q.1.2)) :=
      ((continuous_fst.comp continuous_fst).sub continuous_snd).prodMk
        (continuous_snd.comp continuous_fst)
    exact (hf.comp_measurable hmapf.measurable).mul (hg.comp_measurable hmapg.measurable)
  exact hInt.integral_prod_right'.aestronglyMeasurable

/-- **Coordinate-level joint source lemma.**  If both trajectories are
jointly strongly measurable in the coordinates `(ξ, t) ↦ u t ξ i` on the
horizon product measure, then their genuine Leray-projected Navier source
is jointly `(ξ, t)`-a.e. strongly measurable. -/
theorem continuousNavierSource_joint_aestronglyMeasurable_of_coordSM (T : ℝ)
    (u v : ℝ → ES → ComplexSpace)
    (hu : ∀ j : Fin 3, StronglyMeasurable (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (leiLinTimeMeasure T)) := by
  set μ : Measure (ES × ℝ) := volume.prod (leiLinTimeMeasure T)
  have hconv (i j : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      ((fun η : ES => u p.2 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => v p.2 η i)) p.1) μ :=
    aestronglyMeasurable_convolution_pair (μ := μ) (fun s η => u s η j) (fun s η => v s η i)
      (hu j) (hv i)
  have hraw : AEStronglyMeasurable (fun p : ES × ℝ =>
      rawNavierConvection (u p.2) (v p.2) p.1) μ := by
    apply (aemeasurable_pi_lambda _ ?_).aestronglyMeasurable
    intro i
    change AEMeasurable (fun p : ES × ℝ => ∑ j : Fin 3, (p.1 j : ℂ) *
      ((fun η : ES => u p.2 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => v p.2 η i)) p.1) μ
    exact (Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => by
      have hcoord : Continuous (fun p : ES × ℝ => (p.1 j : ℝ)) :=
        (PiLp.continuous_apply 2 _ j).comp continuous_fst
      exact ((Complex.continuous_ofReal.comp hcoord).aestronglyMeasurable).mul
        (hconv i j))).aemeasurable
  have hrawE : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)) μ :=
    (PiLp.continuous_toLp 2 _).aestronglyMeasurable.comp_aemeasurable hraw.aemeasurable
  have hphase : AEStronglyMeasurable (fun p : ES × ℝ =>
      Complex.I • complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)) μ :=
    hrawE.const_smul (Complex.I : ℂ)
  let w : ES × ℝ → ContinuousLeiLinSpace.ComplexE3 := fun p =>
    Complex.I • complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)
  have hq : Continuous (fun p : ES × ℝ => complexFrequency (spaceProj p.1)) :=
    continuous_complexFrequency.comp (spaceProj.continuous.comp continuous_fst)
  have hqM : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexFrequency (spaceProj p.1)) μ := hq.aestronglyMeasurable
  have hden : AEStronglyMeasurable (fun p : ES × ℝ =>
      ((‖complexFrequency (spaceProj p.1)‖ ^ 2 : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (hq.norm.pow 2)).aestronglyMeasurable
  have hformula : (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1)) =
      fun p => w p -
        (inner ℂ (complexFrequency (spaceProj p.1)) (w p) /
          ((‖complexFrequency (spaceProj p.1)‖ ^ 2 : ℝ) : ℂ)) •
          complexFrequency (spaceProj p.1) := by
    funext p
    change complexEuclideanPoint (ComplexLerayProjection.complexLeray (spaceProj p.1)
      (Complex.I • rawNavierConvection (u p.2) (v p.2) p.1)) = _
    rw [complexEuclideanPoint_complexLeray, complexEuclideanLeray_formula]
    simp [w, complexEuclideanPoint, WithLp.toLp_smul]
  rw [hformula]
  simp only [div_eq_mul_inv]
  exact hphase.sub ((hqM.inner hphase).mul hden.inv₀ |>.smul hqM)

/-- **Shared joint-proxy transport.**  If jointly strongly measurable
frequency fields `wu`, `wv` on `ES × ℝ` represent the trajectories `u`, `v`
by time sections almost everywhere, then the genuine Leray-projected Navier
source of `u`, `v` is jointly `(ξ, t)`-a.e. strongly measurable.  The proof
builds the source measurability from the coordinate sections of the proxies
and transfers along the section equalities: a.e. equality of two
integrands makes their Bochner convolutions equal as functions
(`convolution_congr`), so the genuine source agrees with the proxy source
off a time strip of measure zero. -/
theorem continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies (T : ℝ)
    (u v : ℝ → ES → ComplexSpace)
    (wu wv : ES × ℝ → FourierCoordinateL1)
    (hwu : StronglyMeasurable wu) (hwv : StronglyMeasurable wv)
    (hau : ∀ᵐ t ∂leiLinTimeMeasure T,
        (fun ξ : ES => (wu (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume] u t)
    (hav : ∀ᵐ t ∂leiLinTimeMeasure T,
        (fun ξ : ES => (wv (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume] v t) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (leiLinTimeMeasure T)) := by
  set μ : Measure (ES × ℝ) := volume.prod (leiLinTimeMeasure T)
  set u' : ℝ → ES → ComplexSpace := fun s η => (wu (η, s) : Fin 3 → ℂ)
  set v' : ℝ → ES → ComplexSpace := fun s η => (wv (η, s) : Fin 3 → ℂ)
  have hu' (j : Fin 3) : StronglyMeasurable (fun p : ES × ℝ => u' p.2 p.1 j) :=
    (PiLp.continuous_apply 1 (fun _ : Fin 3 => ℂ) j).comp_stronglyMeasurable hwu
  have hv' (i : Fin 3) : StronglyMeasurable (fun p : ES × ℝ => v' p.2 p.1 i) :=
    (PiLp.continuous_apply 1 (fun _ : Fin 3 => ℂ) i).comp_stronglyMeasurable hwv
  have hL : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u' v' p.2 p.1)) μ :=
    continuousNavierSource_joint_aestronglyMeasurable_of_coordSM T u' v' hu' hv'
  have hraw_apply (U V : ES → ComplexSpace) (ξ : ES) (i : Fin 3) :
      rawNavierConvection U V ξ i =
        ∑ j : Fin 3, (ξ j : ℂ) *
          ((fun η : ES => U η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η : ES => V η i)) ξ := rfl
  have hS : ∀ (s : ℝ), (fun ξ : ES => (wu (ξ, s) : Fin 3 → ℂ)) =ᵐ[volume] u s →
      (fun ξ : ES => (wv (ξ, s) : Fin 3 → ℂ)) =ᵐ[volume] v s → ∀ ξ : ES,
        complexEuclideanPoint (continuousNavierSource u' v' s ξ) =
          complexEuclideanPoint (continuousNavierSource u v s ξ) := by
    intro s hs ht ξ
    have huu (j : Fin 3) :
        (fun η : ES => (wu (η, s) : Fin 3 → ℂ) j) =ᵐ[volume] fun η => u s η j := by
      filter_upwards [hs] with η h
      exact congrFun h j
    have hvv (i : Fin 3) :
        (fun η : ES => (wv (η, s) : Fin 3 → ℂ) i) =ᵐ[volume] fun η => v s η i := by
      filter_upwards [ht] with η h
      exact congrFun h i
    have hconv (i j : Fin 3) :
        (fun η : ES => (wu (η, s) : Fin 3 → ℂ) j)
            ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η : ES => (wv (η, s) : Fin 3 → ℂ) i) =
          (fun η : ES => u s η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η : ES => v s η i) :=
      convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (huu j) (hvv i)
    have hraw : rawNavierConvection (u' s) (v' s) ξ = rawNavierConvection (u s) (v s) ξ := by
      refine funext fun i => ?_
      rw [hraw_apply (u' s) (v' s) ξ i, hraw_apply (u s) (v s) ξ i]
      refine Finset.sum_congr rfl fun j _ => congrArg (HMul.hMul (ξ j : ℂ)) ?_
      exact congrFun (hconv i j) ξ
    refine congrArg complexEuclideanPoint ?_
    change ComplexLerayProjection.complexLeray (spaceProj ξ)
        (Complex.I • rawNavierConvection (u' s) (v' s) ξ) =
        ComplexLerayProjection.complexLeray (spaceProj ξ)
          (Complex.I • rawNavierConvection (u s) (v s) ξ)
    rw [hraw]
  have hsect : ∀ᵐ s ∂leiLinTimeMeasure T, ∀ ξ : ES,
      complexEuclideanPoint (continuousNavierSource u' v' s ξ) =
        complexEuclideanPoint (continuousNavierSource u v s ξ) := by
    filter_upwards [hau, hav] with s hs ht
    exact hS s hs ht
  set B : Set ℝ := {s : ℝ | ¬(∀ ξ : ES,
      complexEuclideanPoint (continuousNavierSource u' v' s ξ) =
        complexEuclideanPoint (continuousNavierSource u v s ξ))}
  have hB : (leiLinTimeMeasure T) B = 0 := ae_iff.mpr hsect
  refine hL.congr (ae_iff.mpr (measure_mono_null (t := Prod.snd ⁻¹' B) ?_ ?_))
  · rintro ⟨ξ, s⟩ h
    exact fun hall => h (hall ξ)
  · have heq : μ (Prod.snd ⁻¹' B) =
      (volume : Measure ES) Set.univ * (leiLinTimeMeasure T) B := by
      rw [show Prod.snd ⁻¹' B = Set.univ ×ˢ B from by ext q; simp,
        Measure.prod_prod Set.univ B]
    rw [heq, hB]
    exact mul_zero _

/-- **Box proxy builder.**  Every completed linked box element carries a
jointly strongly measurable frequency field whose time sections represent
its everywhere `X⁻¹` raw representative a.e. in horizon time: the `L¹`
version of the `L∞` slot obtained from the S1 primitive. -/
theorem exists_jointVersion_everywhereRawRepresentative (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    ∃ w : ES × ℝ → FourierCoordinateL1,
      StronglyMeasurable w ∧
        ∀ᵐ t ∂leiLinTimeMeasure T,
          (fun ξ : ES => (w (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume]
            everywhereRawRepresentative ν T x.1 t := by
  obtain ⟨w, hSM, hsec⟩ :=
    exists_stronglyMeasurable_jointVersion xm1FrequencyMeasure (leiLinTimeMeasure T)
      (by unfold xm1FrequencyMeasure; exact inferInstance) inferInstance
      (lpTopToLpOne (leiLinTimeMeasure T) (x.1.1.fst : Xm1TimeSlot T))
  refine ⟨w, hSM, ?_⟩
  have hac : volume ≪ xm1FrequencyMeasure :=
    (volume_absolutelyContinuous_commonFrequencyMeasure ν hν).trans
      (Measure.absolutelyContinuous_of_le (commonFrequencyMeasure_le_xm1 ν))
  filter_upwards [hsec, everywhereRawRepresentative_eq_xm1_ae ν hν T x.1] with t hs ht
  filter_upwards [eventually_of_eventually_of_ac hac hs] with ξ hξ
  show (w (ξ, t) : Fin 3 → ℂ) = everywhereRawRepresentative ν T x.1 t ξ
  exact (congrArg (fun z : FourierCoordinateL1 => (z : Fin 3 → ℂ)) hξ).trans
    ((rfl : (⇑(lpTopToLpOne (leiLinTimeMeasure T) (x.1.1.fst : Xm1TimeSlot T)) t ξ : Fin 3 → ℂ)
        = xm1RawRepresentative ν T x.1 t ξ).trans (congrFun ht ξ).symm)

/-- Leaf `hjointDiag`: joint `(ξ, t)`-a.e. strong measurability of the
diagonal Leray-projected Navier source of every box element, for general
quotient-represented carriers. -/
theorem mildLeafHjointDiag (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T x.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  obtain ⟨w, hSM, hsec⟩ := exists_jointVersion_everywhereRawRepresentative ν hν T R x
  exact continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies T
    (everywhereRawRepresentative ν T x.1) (everywhereRawRepresentative ν T x.1)
    w w hSM hSM hsec hsec

/-- Leaf `hjointL`: joint a.e. strong measurability of the LEFT ordered
mixed source `(rep x − rep y, rep x)`. -/
theorem mildLeafHjointL (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x y : ActualLinkedBox ν T (2 * R) (2 * R)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (commonRepresentativeDifference ν T x.1 y.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  obtain ⟨wx, hxSM, hx⟩ := exists_jointVersion_everywhereRawRepresentative ν hν T R x
  obtain ⟨wy, hySM, hy⟩ := exists_jointVersion_everywhereRawRepresentative ν hν T R y
  set wdiff : ES × ℝ → FourierCoordinateL1 := fun p => wx p - wy p
  have hSM : StronglyMeasurable wdiff := hxSM.sub hySM
  have hsec : ∀ᵐ t ∂leiLinTimeMeasure T,
      (fun ξ : ES => (wdiff (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume]
        commonRepresentativeDifference ν T x.1 y.1 t := by
    filter_upwards [hx, hy] with t hs ht
    show (fun ξ : ES => (wdiff (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume]
        commonRepresentativeDifference ν T x.1 y.1 t
    exact hs.sub ht
  exact continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies T
    (commonRepresentativeDifference ν T x.1 y.1) (everywhereRawRepresentative ν T x.1)
    wdiff wx hSM hxSM hsec hx

/-- Leaf `hjointR`: joint a.e. strong measurability of the RIGHT ordered
mixed source `(rep y, rep x − rep y)`. -/
theorem mildLeafHjointR (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x y : ActualLinkedBox ν T (2 * R) (2 * R)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T y.1)
          (commonRepresentativeDifference ν T x.1 y.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  obtain ⟨wx, hxSM, hx⟩ := exists_jointVersion_everywhereRawRepresentative ν hν T R x
  obtain ⟨wy, hySM, hy⟩ := exists_jointVersion_everywhereRawRepresentative ν hν T R y
  set wdiff : ES × ℝ → FourierCoordinateL1 := fun p => wx p - wy p
  have hSM : StronglyMeasurable wdiff := hxSM.sub hySM
  have hsec : ∀ᵐ t ∂leiLinTimeMeasure T,
      (fun ξ : ES => (wdiff (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume]
        commonRepresentativeDifference ν T x.1 y.1 t := by
    filter_upwards [hx, hy] with t hs ht
    show (fun ξ : ES => (wdiff (ξ, t) : Fin 3 → ℂ)) =ᵐ[volume]
        commonRepresentativeDifference ν T x.1 y.1 t
    exact hs.sub ht
  exact continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies T
    (everywhereRawRepresentative ν T y.1) (commonRepresentativeDifference ν T x.1 y.1)
    wy wdiff hySM hSM hy hsec

/-! ### Open boundary, as two named sub-records

The pointwise-in-time mild-image moment leaves and the polarization
decomposition leaves are *not* derived by this module.  Their honest
obstruction is recorded in the module header discussion of this section:
the record fields `hmM`, `hmXm1`, `hmX1` quantify over *every* real time and
require, at `t < 0`, pointwise `X^{±1}` integrability of the backward heat
flow applied to an arbitrary admissible `a`; the heat multiplier
`exp(ν ‖ξ‖² t)` explodes there while `ha`/`ha1` supply only polynomial
control, so no constructor can derive them from the given hypotheses.  The
remaining record fields are therefore packaged verbatim into two named
sub-records, and `mildAssemblyLeaves_of_namedLeaves` shows the record is
equivalent to the trio above plus these sub-records.
-/

/-- The pointwise-in-time mild-image leaves: the six fields of
`MildAssemblyLeaves` that quantify over every real time (spatial moment
integrability at every `t`, the two time-section measurabilities, and the
time integrability of the `X¹` mass).  These are the exact remaining
propositions behind the mild fixed point constructor. -/
structure MildAssemblyTimeLeaves
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R) where
  /-- Leaf 2a: pointwise spatial measurability of the mild image. -/
  hmM : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t i,
      AEStronglyMeasurable (fun ξ : ES =>
        mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i) volume
  /-- Leaf 2b: pointwise `X⁻¹` integrability of the mild image. -/
  hmXm1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t i,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2c: pointwise `X¹` integrability of the mild image. -/
  hmX1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t i,
      Integrable (fun ξ : ES => ‖ξ‖ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2d: strong measurability of the `X⁻¹`-valued time section. -/
  hmXm1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (xm1Section (mildImage ν hν a (everywhereRawRepresentative ν T x.1))
          (hmM x) (hmXm1 x)) (leiLinTimeMeasure T)
  /-- Leaf 2e: strong measurability of the viscous `X¹`-valued time section. -/
  hmX1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (viscousX1Section (mildImage ν hν a (everywhereRawRepresentative ν T x.1))
          (hmM x) (hmX1 x) ν) (leiLinTimeMeasure T)
  /-- Leaf 2f: time integrability of the mild image's `X¹` mass. -/
  hmX1Int : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      Integrable (fun t : ℝ => coordinateX1Mass
        (mildImage ν hν a (everywhereRawRepresentative ν T x.1) t))
        (leiLinTimeMeasure T)

/-- The polarization decomposition leaves: the two `a.e.`-in-time budget
identities of `MildAssemblyLeaves`. -/
structure MildAssemblyPolarizationLeaves
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R) where
  /-- Leaf 3a: the polarization decomposition of the `X⁻¹` mass of the mild
  difference into the two Duhamel slots, a.e. in time. -/
  hXmDiff : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      ∀ᵐ t ∂leiLinTimeMeasure T,
        coordinateXm1Mass (fun ξ : ES =>
            mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
              mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ) ≤
          coordinateXm1Mass (continuousDuhamel (ν : ℝ)
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) t) +
            coordinateXm1Mass (continuousDuhamel (ν : ℝ)
              (everywhereRawRepresentative ν T y.1)
              (commonRepresentativeDifference ν T x.1 y.1) t)
  /-- Leaf 3b: the same decomposition for the viscous `X¹` spacetime budget. -/
  hX1Diff : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ : ES =>
          mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
            mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ)
          ∂(volume.restrict (Icc (0 : ℝ) T)) ≤
        (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) t)
          ∂(volume.restrict (Icc (0 : ℝ) T)) +
          (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
              (everywhereRawRepresentative ν T y.1)
              (commonRepresentativeDifference ν T x.1 y.1) t)
          ∂(volume.restrict (Icc (0 : ℝ) T))

/-- The assembly record is exactly: the three joint-source leaves (closed in
this module for general box elements), the threshold `hRν`, and the two
named sub-records above (the honest open boundary). -/
theorem mildAssemblyLeaves_of_namedLeaves (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (hRν : R ≤ (ν : ℝ) / 16)
    (time : MildAssemblyTimeLeaves ν hν T R hT a haM ha ha1 haR)
    (pol : MildAssemblyPolarizationLeaves ν hν T R hT a haM ha ha1 haR) :
    MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR where
  hRν := hRν
  hjointDiag := mildLeafHjointDiag ν hν T R
  hmM := time.hmM
  hmXm1 := time.hmXm1
  hmX1 := time.hmX1
  hmXm1Time := time.hmXm1Time
  hmX1Time := time.hmX1Time
  hmX1Int := time.hmX1Int
  hjointL := mildLeafHjointL ν hν T R
  hjointR := mildLeafHjointR ν hν T R
  hXmDiff := pol.hXmDiff
  hX1Diff := pol.hX1Diff

/-- Forward projection: the time leaves read off an assembly record.  With
`mildAssemblyLeaves_of_namedLeaves` this makes the equivalence claim in the
assembly theorem's docstring literal: the record *is* the closed triple plus
`hRν` plus these two named sub-records, in both directions. -/
theorem mildAssemblyTimeLeaves_of (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR) :
    MildAssemblyTimeLeaves ν hν T R hT a haM ha ha1 haR where
  hmM := L.hmM
  hmXm1 := L.hmXm1
  hmX1 := L.hmX1
  hmXm1Time := L.hmXm1Time
  hmX1Time := L.hmX1Time
  hmX1Int := L.hmX1Int

/-- Forward projection: the polarization leaves read off an assembly record. -/
theorem mildAssemblyPolarizationLeaves_of (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR) :
    MildAssemblyPolarizationLeaves ν hν T R hT a haM ha ha1 haR where
  hXmDiff := L.hXmDiff
  hX1Diff := L.hX1Diff

-- Receipts: every new top-level declaration with its elaborated type and raw axioms.
#check @eventually_of_eventually_of_ac
#print axioms eventually_of_eventually_of_ac
#check @spatialCover
#print axioms spatialCover
#check @spatialCover_stronglyMeasurable
#print axioms spatialCover_stronglyMeasurable
#check @spatialCover_ae_eq
#print axioms spatialCover_ae_eq
#check @exists_stronglyMeasurable_jointVersion
#print axioms exists_stronglyMeasurable_jointVersion
#check @aestronglyMeasurable_convolution_pair
#print axioms aestronglyMeasurable_convolution_pair
#check @continuousNavierSource_joint_aestronglyMeasurable_of_coordSM
#print axioms continuousNavierSource_joint_aestronglyMeasurable_of_coordSM
#check @continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies
#print axioms continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies
#check @exists_jointVersion_everywhereRawRepresentative
#print axioms exists_jointVersion_everywhereRawRepresentative
#check @mildLeafHjointDiag
#print axioms mildLeafHjointDiag
#check @mildLeafHjointL
#print axioms mildLeafHjointL
#check @mildLeafHjointR
#print axioms mildLeafHjointR
#check @MildAssemblyTimeLeaves
#check @MildAssemblyTimeLeaves.mk
#print axioms MildAssemblyTimeLeaves.mk
#check @MildAssemblyPolarizationLeaves
#check @MildAssemblyPolarizationLeaves.mk
#print axioms MildAssemblyPolarizationLeaves.mk
#check @mildAssemblyLeaves_of_namedLeaves
#print axioms mildAssemblyLeaves_of_namedLeaves
end Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
