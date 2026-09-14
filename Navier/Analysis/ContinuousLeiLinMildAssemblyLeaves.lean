import Navier.Analysis.ContinuousLeiLinMildFixedPoint
import Navier.Analysis.ContinuousLeiLinActualPolarization
import Navier.Analysis.ContinuousLeiLinBoxD3Maximal
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
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinMixedX1
open Navier.Analysis.ContinuousLeiLinBoxD3Measurability
open Navier.Analysis.ContinuousLeiLinBoxD3Output
open Navier.Analysis.ContinuousLeiLinBoxD3Maximal
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinBoxB1Joint

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

/-! ## S3: pointwise-time mild-image leaves for general box elements (step 3)

Leaves `hmM` (2a), `hmXm1` (2b) and `hmX1Int` (2f) are DERIVED here for
every element of the actual linked box, on the horizon `t ∈ Icc 0 T` where
the heat multiplier `exp(-ν ‖ξ‖² t)` decays rather than explodes.  Each
per-time Duhamel spatial fact is obtained by integrating the joint
`(ξ, s)`-measurable (or joint-integrable) heat-weighted source over the
causal interval, through `AEStronglyMeasurable.integral_prod_right'` and
`Integrable.integral_prod_left`; the heat part is dominated by the datum's
own moment because the multiplier is `≤ 1` for `t ≥ 0`.  The `X¹`-mass leaf
(2f) is the almost-everywhere-time maximal-regularity package: the
actual-box `D₃` block of `ContinuousLeiLinBoxD3AE` is replayed with
`mildLeafHjointDiag` as its sole structural input and `Integrable` as its
conclusion, then transported to the horizon truncation.

What S3 does NOT derive: the pointwise `X¹` leaf `hmX1` at every horizon
time (maximal regularity supplies its Duhamel part `μ`-a.e. in `t`, never at
every `t` — stated exactly below the theorems), and neither section leaf at
this step — but the `X⁻¹` section leaf `hmXm1Time` (2d) is supplied next,
in S4, as a continuity bootstrap, while `hmX1Time` (2e) remains open with
the surviving proposition recorded in the obstruction comment below. -/

/-- Leaf 2a for general boxes: spatial measurability of the mild image at
every horizon time. -/
theorem mildTimeLeaf_hmM (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES =>
        mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i) volume := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) :=
    by simpa [u] using mildLeafHjointDiag ν hν T R x
  have hjointT : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) :=
    hjoint.mono_measure
      (Measure.prod_mono le_rfl
        (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
  have hcoord : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 t hjointT i
  show AEStronglyMeasurable
      (fun ξ : ES => heatVec (ν : ℝ) t a ξ i + continuousDuhamel (ν : ℝ) u u t ξ i) volume
  refine AEStronglyMeasurable.add ?_ ?_
  · show AEStronglyMeasurable
        (fun ξ : ES =>
          ((Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i) volume
    exact (by fun_prop :
        AEStronglyMeasurable
          (fun ξ : ES => ((Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)) volume)
      |>.mul (haM i)
  · have hjointW : AEStronglyMeasurable (fun p : ES × ℝ =>
        ((Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t - p.2)) : ℝ) : ℂ) *
          continuousNavierSource u u p.2 p.1 i))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) :=
      (by fun_prop :
          AEStronglyMeasurable
            (fun p : ES × ℝ =>
              ((Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t - p.2)) : ℝ) : ℂ)))
            (volume.prod (volume.restrict (Icc (0 : ℝ) t)))).mul hcoord
    exact hjointW.integral_prod_right'

/-- Leaf 2b for general boxes: `X⁻¹` integrability of the mild image at
every horizon time.  The Duhamel majorant is the `ξ`-marginal of the joint
weighted-source integrability `integrable_weightedContinuousNavierSource_coord_of_actualBox`
(the heat multiplier is `≤ 1` on the causal interval `s ≤ t ≤ T`). -/
theorem mildTimeLeaf_hmXm1 (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1
  let μt := volume.restrict (Icc (0 : ℝ) t)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hjointT : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod μt) :=
    (mildLeafHjointDiag ν hν T R x).mono_measure
      (Measure.prod_mono le_rfl
        (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
  have hcoord : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μt) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 t hjointT i
  have hsrc : Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
      ‖continuousNavierSource u u p.2 p.1 i‖) (volume.prod μt) :=
    integrable_weightedContinuousNavierSource_coord_of_actualBox ν hν T (2 * R) (2 * R) x
      t ht hjointT i
  -- heat part, dominated by the datum: the multiplier is ≤ 1 at t ≥ 0
  have hheat : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatVec (ν : ℝ) t a ξ i‖) := by
    have hform (ξ : ES) : ‖ξ‖⁻¹ * ‖heatVec (ν : ℝ) t a ξ i‖ =
        Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖a ξ i‖) := by
      show ‖ξ‖⁻¹ * ‖heatMode (ν : ℝ) t (fun ζ : ES => a ζ i) ξ‖ = _
      rw [norm_heatMode_eq]
      ring
    have hfactor : AEStronglyMeasurable
        (fun ξ : ES => Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * t))) volume := by fun_prop
    refine ((ha i).mono' (hfactor.mul (ha i).aestronglyMeasurable) ?_).congr
      (Filter.Eventually.of_forall fun ξ => (hform ξ).symm)
    filter_upwards with ξ
    have hbase : 0 ≤ ‖ξ‖⁻¹ * ‖a ξ i‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)
    have hexp : Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) ht.1))
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hbase)]
    nlinarith [hexp, hbase]
  -- Duhamel part: dominated by the ξ-marginal of the joint weighted source
  have hM : Integrable
      (fun ξ : ES => ∫ s, ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖ ∂μt) volume :=
    hsrc.integral_prod_left
  have hDle : ∀ᵐ ξ ∂volume, ‖ξ‖⁻¹ * ‖continuousDuhamel (ν : ℝ) u u t ξ i‖ ≤
      ∫ s in Icc (0 : ℝ) t, ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖ ∂volume := by
    filter_upwards [hsrc.prod_right_ae] with ξ hξ
    refine le_trans (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (inv_nonneg.mpr (norm_nonneg ξ))) ?_
    rw [← smul_eq_mul, ← MeasureTheory.integral_smul]
    refine integral_mono_of_nonneg
      (ae_of_all _ fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
      hξ (by
        filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with s hs
        rw [norm_heatMode_eq]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg ξ))
        have hexp : Real.exp (-((ν : ℝ) * ‖ξ‖ ^ 2 * (t - s))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg
            (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr hs.2)))
        nlinarith [hexp, norm_nonneg (continuousNavierSource u u s ξ i)])
  have hjointW : AEStronglyMeasurable (fun p : ES × ℝ =>
      heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => continuousNavierSource u u p.2 ζ i) p.1)
      (volume.prod μt) := by
    show AEStronglyMeasurable (fun p : ES × ℝ =>
        ((Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t - p.2)) : ℝ) : ℂ) *
          continuousNavierSource u u p.2 p.1 i)) (volume.prod μt)
    exact (by fun_prop : AEStronglyMeasurable (fun p : ES × ℝ =>
        ((Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t - p.2)) : ℝ) : ℂ))) (volume.prod μt)).mul hcoord
  have hDAES : AEStronglyMeasurable
      (fun ξ : ES => continuousDuhamel (ν : ℝ) u u t ξ i) volume := by
    show AEStronglyMeasurable (fun ξ : ES => ∫ s in Icc (0 : ℝ) t,
        heatMode (ν : ℝ) (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i) ξ) volume
    exact hjointW.integral_prod_right'
  have hDmajor : Integrable
      (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousDuhamel (ν : ℝ) u u t ξ i‖) volume := by
    refine (hM.mono'
      ((by fun_prop : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹) volume).mul hDAES.norm) ?_)
    filter_upwards [hDle] with ξ h
    rw [Real.norm_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))]
    exact h
  refine (hheat.add hDmajor).mono'
    ((by fun_prop : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹) volume).mul
      (mildTimeLeaf_hmM ν hν T R a haM x t ht i).norm) ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))]
  simp only [Pi.add_apply]
  show ‖ξ‖⁻¹ * ‖heatVec (ν : ℝ) t a ξ i + continuousDuhamel (ν : ℝ) u u t ξ i‖ ≤
    ‖ξ‖⁻¹ * ‖heatVec (ν : ℝ) t a ξ i‖ + ‖ξ‖⁻¹ * ‖continuousDuhamel (ν : ℝ) u u t ξ i‖
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    (inv_nonneg.mpr (norm_nonneg ξ))).trans ?_
  rw [mul_add]

/-- The `D₃` maximal-regularity package for the diagonal source of a general
box element, replaying the internal block of
`ContinuousLeiLinBoxD3AE` with `mildLeafHjointDiag` as its sole structural
input: the Duhamel `L¹_t(X¹)` coordinate masses are time-integrable and
spatially `X¹`-integrable at almost every horizon time. -/
private theorem mildTimeLeaf_d3X1 (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∀ i : Fin 3, Integrable (fun t : ℝ => normX1 (fun ξ : ES =>
        continuousDuhamel (ν : ℝ) (everywhereRawRepresentative ν T x.1)
          (everywhereRawRepresentative ν T x.1) t ξ i))
        (volume.restrict (Icc (0 : ℝ) T))) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i‖)) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod μ) :=
    mildLeafHjointDiag ν hν T R x
  have hcoord (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 T
      (by simpa [u, μ] using hjoint) i
  have hDjoint (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel (ν : ℝ) u u p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable (ν : ℝ) T u u i (hcoord i)
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_coord_of_actualBox
      ν hν T (2 * R) (2 * R) x T ⟨hT, le_rfl⟩
      (by simpa [u, μ] using mildLeafHjointDiag ν hν T R x) i
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) by fun_prop).mul (hcoord i).norm).aemeasurable)
  obtain ⟨_, hb0⟩ := continuousNavierSource_fixedTime_inputs_of_actualBox
    ν hν T (2 * R) (2 * R) x
  have hW1 (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun u u i (ν : ℝ) p.1 r p.2)
      (volume.prod μ) := by
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource u u p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoord i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hW (i : Fin 3) : AEMeasurable
      (fun z : ℝ × (ES × ℝ) => mixedKernelFun u u i (ν : ℝ) z.2.1 z.1 z.2.2)
      (μ.prod (volume.prod μ)) := by
    have hcoord3 : AEStronglyMeasurable (fun z : ℝ × (ES × ℝ) =>
        continuousNavierSource u u z.2.2 z.2.1 i)
        (μ.prod (volume.prod μ)) :=
      (hcoord i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun z : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource u u z.2.2 z.2.1 i‖ *
        (if z.2.2 ≤ z.1 then ENNReal.ofReal
          (‖z.2.1‖ * Real.exp (-((ν : ℝ) * ‖z.2.1‖ ^ 2 *
            (z.1 - z.2.2)))) else 0))
      (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hDfacts (i : Fin 3) := continuousDuhamel_X1_integrability
    u u (ν : ℝ) T i hνR (hDjoint i) (hW1 i) (hW i)
      (fun s _ => hb0 s i) (hg i) (hJ i)
  exact ⟨fun i => (hDfacts i).1, Filter.eventually_all.mpr fun i => (hDfacts i).2⟩

/-- Leaf 2c for general boxes in its maximal honest form: the `X¹`
integrability of the mild image at **almost every** horizon time.  The heat
part holds at every `t ≥ 0`; the Duhamel part comes from `D₃` maximal
regularity, which supplies its spatial `X¹` integrability only
`volume.restrict (Icc 0 T)`-almost everywhere in `t`. -/
theorem mildTimeLeaf_hmX1_ae (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    ∀ᵐ t ∂leiLinTimeMeasure T, ∀ i : Fin 3, Integrable (fun ξ : ES =>
      ‖ξ‖ * ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨_, hDξall⟩ := mildTimeLeaf_d3X1 ν hν T R hT x
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet, hDξall] with t ht hDξt
  intro i
  refine ((integrable_weighted_heatMode_of_X1 (fun ζ : ES => a ζ i) (ha1 i)
      (ν : ℝ) t hνR ht.1).add (hDξt i)).mono'
    ((by fun_prop : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖) volume).mul
      (mildTimeLeaf_hmM ν hν T R a haM x t ht i).norm) ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg ξ) (norm_nonneg _))]
  show ‖ξ‖ * ‖heatVec (ν : ℝ) t a ξ i + continuousDuhamel (ν : ℝ) u u t ξ i‖ ≤
    ‖ξ‖ * ‖heatVec (ν : ℝ) t a ξ i‖ + ‖ξ‖ * ‖continuousDuhamel (ν : ℝ) u u t ξ i‖
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg ξ)).trans
    ((mul_add _ _ _).le)

/-- Leaf 2f for general boxes: time integrability of the `X¹` mass of the
horizon-truncated mild image.  The `a.e.`-time `D₃` package
`mildTimeLeaf_d3X1` supplies the Duhamel `L¹_t(X¹)` part, the datum its heat
part, and `Integrable.congr` transports the conclusion from
`continuousMildImage` to the truncation `mildImageIcc`. -/
theorem mildTimeLeaf_hmX1Int (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    Integrable (fun t : ℝ => coordinateX1Mass
      (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t))
      (leiLinTimeMeasure T) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨hD0, hDξall⟩ := mildTimeLeaf_d3X1 ν hν T R hT x
  have hImeas : AEStronglyMeasurable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) hνR a u t)) μ :=
    coordinateX1Mass_continuousMildImage_aestronglyMeasurable
      (ν : ℝ) T hνR a haM u (mildLeafHjointDiag ν hν T R x)
  have hHt : Integrable (fun t : ℝ => coordinateX1Mass
      (heatVec (ν : ℝ) t a)) μ :=
    integrable_coordinateX1Mass_heatVec_on_Icc a ha1 (ν : ℝ) T hνR
  have hDt : Integrable (fun t : ℝ => coordinateX1Mass
      (continuousDuhamel (ν : ℝ) u u t)) μ := by
    unfold coordinateX1Mass
    exact integrable_finsetSum (f := fun i (t : ℝ) =>
      normX1 (fun ξ : ES => continuousDuhamel (ν : ℝ) u u t ξ i))
      Finset.univ (fun i _ => hD0 i)
  have hIt : Integrable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) hνR a u t)) μ := by
    apply (hHt.add hDt).mono' hImeas
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet, hDξall] with t ht hDξt
    have hle := coordinateX1Mass_add_le (heatVec (ν : ℝ) t a)
      (continuousDuhamel (ν : ℝ) u u t)
      (fun i => integrable_weighted_heatMode_of_X1
        (fun ξ : ES => a ξ i) (ha1 i) (ν : ℝ) t hνR ht.1)
      hDξt
    rw [Real.norm_of_nonneg
      (Navier.Analysis.ContinuousLeiLinBoxProduct.coordinateX1Mass_nonneg _)]
    change coordinateX1Mass (fun ξ => heatVec (ν : ℝ) t a ξ +
      continuousDuhamel (ν : ℝ) u u t ξ) ≤ _
    exact hle
  have htrunc : (fun t : ℝ => coordinateX1Mass (continuousMildImage (ν : ℝ) hνR a u t)) =ᵐ[μ]
      fun t : ℝ => coordinateX1Mass (mildImageIcc ν hν T a u t) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    exact congrArg coordinateX1Mass (funext fun ξ =>
      (mildImageIcc_of_mem ν hν T a u t ht ξ).symm)
  exact hIt.congr htrunc

/-! ## S4: the section leaf `hmXm1Time` (2d) — continuity bootstrap

The S3 leaves give the spatial facts at every horizon time.  The missing
`Lp`-valued time measurability of the quotient-represented mild image is
derived here as a *continuity* statement, not a measurability construction:
the section map

    Φ : s ↦ toXm1Spatial (mild image at s)

is continuous on the horizon `Icc 0 T`.  At `t₀ ∈ Icc 0 T` the difference
`Φ s − Φ t₀` is one `toXm1Spatial` of the pointwise difference field
(`toXm1Spatial_sub`), its norm is the coordinate mass of that difference
(`norm_toXm1Spatial`), and the mass splits by the triangle inequality into
the heat part `Σᵢ normXm1 (s⁻¹‖heat s − heat t₀‖)` and the Duhamel part
`Σᵢ normXm1 (s⁻¹‖duh s − duh t₀‖)`.  The heat part goes to `0` coordinate
wise by dominated convergence against the datum `‖ξ‖⁻¹‖a ξ i‖`: the heat
multiplier `exp(-ν‖ξ‖²s)` is continuous in `s` and `∈ [0,1]` for `s ≥ 0`.
The Duhamel part is squeezed by rewriting each interval integral as an
indicator integral against the horizon measure
(`integral_Icc_eq_horizon_indicator`) and using, pointwise a.e. in `ξ`,

    ‖ξ‖⁻¹‖duh s ξ i − duh t₀ ξ i‖ ≤ ∫ r, H s (ξ, r) ∂(vol|Icc 0 T)

with `H s (ξ,r)` the causal-truncation difference
`|1[r≤s]e^{-ν‖ξ‖²(s−r)} − 1[r≤t₀]e^{-ν‖ξ‖²(t₀−r)}| · ‖ξ‖⁻¹‖src r ξ i‖ ≤`
the joint weighted-source integrability
`integrable_weightedContinuousNavierSource_coord_of_actualBox` (the
fiber `aes` facts come from `AEStronglyMeasurable.prodMk_left`).
Dominated convergence on the product measure kills `∫ (ξ,r), H s` as
`s → t₀`: `H s → 0` off the null fiber `r = t₀` (both indicators flip
together in the limit, or are `0` near `r > t₀`).  A continuous map into a
pseudo-metrizable space is `AEStronglyMeasurable` (`Continuous.aestronglyMeasurable`,
no `Lp` separability needed), precomposition with the continuous retraction
`t ↦ max 0 (min t T)` and `mono_measure` transfer `AES` from `volume` to
its horizon restriction, and `toXm1Spatial_congr_raw` glues the
`mildImageIcc` zero extension back in almost everywhere. -/

/-- The `X⁻¹` spatial quotient does not depend on the measurability or
integrability proofs attached to the field, nor on the choice of a pointwise
representative. -/
private theorem toXm1Spatial_congr_raw {f g : ES → ComplexSpace}
    (hfM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => f ξ i) volume)
    (hgM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => g ξ i) volume)
    (hfI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ i‖))
    (hgI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ i‖))
    (hfg : ∀ ξ : ES, f ξ = g ξ) :
    toXm1Spatial f hfM hfI = toXm1Spatial g hgM hgI := by
  -- derivation: both sides are `MemLp.toLp` of the coordinate field;
  -- `toLp_congr` identifies the quotients under any a.e. equality.
  unfold toXm1Spatial
  exact MemLp.toLp_congr _ _
    (ae_of_all _ fun ξ => congrArg (WithLp.toLp 1) (hfg ξ))

@[simp]
private theorem coordinateL1_sub (f g : ES → ComplexSpace) (ξ : ES) :
    coordinateL1 f ξ - coordinateL1 g ξ = coordinateL1 (fun ξ => f ξ - g ξ) ξ := rfl

/-- Weighted difference integrability, coordinatewise. -/
private theorem xm1_integrable_diff (f g : ES → ComplexSpace)
    (hfM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => f ξ i) volume)
    (hgM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => g ξ i) volume)
    (hfI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ i‖))
    (hgI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ i‖))
    (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(fun ξ => f ξ - g ξ) ξ i‖) := by
  -- derivation: w‖f−g‖ ≤ w‖f‖ + w‖g‖ pointwise.
  refine ((hfI i).add (hgI i)).mono'
    ((by fun_prop : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹) volume).mul
      ((hfM i).sub (hgM i)).norm) ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))]
  show ‖ξ‖⁻¹ * ‖f ξ i - g ξ i‖ ≤ ‖ξ‖⁻¹ * ‖f ξ i‖ + ‖ξ‖⁻¹ * ‖g ξ i‖
  refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _)
    (inv_nonneg.mpr (norm_nonneg ξ))).trans ?_
  rw [mul_add]

/-- Subtraction of two `X⁻¹` quotients is the quotient of the pointwise
difference. -/
private theorem toXm1Spatial_sub (f g : ES → ComplexSpace)
    (hfM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => f ξ i) volume)
    (hgM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => g ξ i) volume)
    (hfI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ i‖))
    (hgI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ i‖)) :
    toXm1Spatial f hfM hfI - toXm1Spatial g hgM hgI =
      toXm1Spatial (fun ξ => f ξ - g ξ)
        (fun i => (hfM i).sub (hgM i))
        (fun i => xm1_integrable_diff f g hfM hgM hfI hgI i) := by
  -- derivation: a.e. in ξ the quotients are `coordinateL1`, and `WithLp.toLp`
  -- is a pointwise homomorphism, so the difference of the quotients equals the
  -- quotient of the pointwise difference.
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (toXm1Spatial f hfM hfI) (toXm1Spatial g hgM hgI),
    coeFn_toXm1Spatial f hfM hfI, coeFn_toXm1Spatial g hgM hgI,
    coeFn_toXm1Spatial (fun ξ => f ξ - g ξ) (fun i => (hfM i).sub (hgM i))
      (fun i => xm1_integrable_diff f g hfM hgM hfI hgI i)] with ξ h0 h1 h2 h3
  have key := coordinateL1_sub f g ξ
  rw [← h1, ← h2, ← h3, ← Pi.sub_apply, ← h0] at key
  exact key

/-- Triangle inequality for the coordinate `X⁻¹` mass. -/
private theorem coordinateXm1Mass_add_le (F G : ES → ComplexSpace)
    (hFI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖F ξ i‖))
    (hGI : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖G ξ i‖))
    (hFG : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(fun ξ => F ξ + G ξ) ξ i‖)) :
    coordinateXm1Mass (fun ξ => F ξ + G ξ) ≤ coordinateXm1Mass F + coordinateXm1Mass G := by
  -- derivation: w‖F+G‖ ≤ w‖F‖ + w‖G‖; the integral of a sum of integrables
  -- is the sum of the integrals; sums distribute.
  unfold coordinateXm1Mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold normXm1
  have hpoint : (fun ξ : ES => ‖ξ‖⁻¹ * ‖(fun ξ => F ξ + G ξ) ξ i‖)
      ≤ fun a : ES => ‖a‖⁻¹ * ‖F a i‖ + ‖a‖⁻¹ * ‖G a i‖ := fun ξ => by
    have hw : 0 ≤ ‖(ξ : ES)‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
    show ‖(ξ : ES)‖⁻¹ * ‖F ξ i + G ξ i‖ ≤
      ‖(ξ : ES)‖⁻¹ * ‖F ξ i‖ + ‖(ξ : ES)‖⁻¹ * ‖G ξ i‖
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) hw).trans ?_
    rw [mul_add]
  rw [← integral_add (hFI i) (hGI i)]
  exact integral_mono (hFG i) ((hFI i).add (hGI i)) hpoint

/-- An interval integral over `[0, t]` (`t` on the horizon) is the indicator
integral of the causal truncation against the horizon measure. -/
private theorem integral_Icc_eq_horizon_indicator (t T : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) (K : ℝ → ℂ) :
    ∫ s in Icc (0 : ℝ) t, K s ∂volume =
      ∫ s, (if s ≤ t then K s else 0) ∂(volume.restrict (Icc (0 : ℝ) T)) := by
  -- derivation: `[0,t] ⊆ [0,T]` so the restrictions agree; on the horizon
  -- `s ∈ [0,t] ↔ s ≤ t`.
  have hinter : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  calc ∫ s in Icc (0 : ℝ) t, K s ∂volume
      = ∫ s in Icc (0 : ℝ) t, K s ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        show ∫ s, K s ∂(volume.restrict (Icc (0 : ℝ) t)) = _
        rw [Measure.restrict_restrict_of_subset hinter]
      _ = ∫ s, (if s ∈ Icc (0 : ℝ) t then K s else 0) ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        rw [(integral_indicator (μ := volume.restrict (Icc (0 : ℝ) T))
          isClosed_Icc.measurableSet).symm]
        congr 1
        funext s
        simp only [Set.indicator_apply]
      _ = ∫ s, (if s ≤ t then K s else 0) ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        refine integral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict isClosed_Icc.measurableSet] with s hs
        refine ite_congr (propext ⟨fun hh => hh.2, fun hh => ⟨hs.1, hh⟩⟩)
          (fun _ => rfl) (fun _ => rfl)

/-- Coordinatewise heat continuity in the `X⁻¹` mass: dominated convergence
against the datum, the multiplier is continuous and `∈ [0,1]` on the
horizon. -/
private theorem tendsto_normXm1_heatVec_sub (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (νR : ℝ) (hνR : 0 < νR) (T t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    Tendsto (fun s : ℝ => normXm1 (fun ξ : ES =>
        heatVec νR s a ξ i - heatVec νR t₀ a ξ i))
      (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 0) := by
  let l := 𝓝[Icc (0 : ℝ) T] t₀
  have hmain : Tendsto (fun s : ℝ => ∫ ξ : ES,
      |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) - Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| *
        (‖ξ‖⁻¹ * ‖a ξ i‖)) l (𝓝 0) := by
    have hlim : ∀ᵐ ξ ∂volume,
        Tendsto (fun s : ℝ => |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) -
            Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| * (‖ξ‖⁻¹ * ‖a ξ i‖)) l (𝓝 0) :=
      ae_of_all _ fun ξ => by
        have hg : Tendsto (fun s : ℝ => -(νR * ‖ξ‖ ^ 2 * s)) l
            (𝓝 (-(νR * ‖ξ‖ ^ 2 * t₀))) :=
          ((continuous_const.mul continuous_id).tendsto t₀).neg.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun s : ℝ =>
            Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) - Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))) l
            (𝓝 (Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀))) -
              Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀))))) :=
          ((Real.continuous_exp.continuousAt.tendsto).comp hg).sub tendsto_const_nhds
        rw [sub_self] at h2
        simpa using (h2.abs).mul tendsto_const_nhds
    have hbnd : ∀ᶠ s in l, ∀ᵐ ξ ∂volume,
        ‖|Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) - Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| *
            (‖ξ‖⁻¹ * ‖a ξ i‖)‖ ≤
          ‖ξ‖⁻¹ * ‖a ξ i‖ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      apply ae_of_all _ fun ξ => by
        have hw : 0 ≤ ‖ξ‖⁻¹ * ‖a ξ i‖ :=
          mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)
        have he1 : Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr
            (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) hs.1))
        have he0 : Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr
            (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) ht₀.1))
        have h1 : 0 ≤ Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) := (Real.exp_pos _).le
        have h0 : 0 ≤ Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀))) := (Real.exp_pos _).le
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hw)]
        have habs : |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) -
            Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| ≤ 1 := by
          rw [abs_le]
          constructor <;> nlinarith
        nlinarith
    have hmeas : ∀ᶠ s in l, AEStronglyMeasurable
        (fun ξ : ES => |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) -
            Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| * (‖ξ‖⁻¹ * ‖a ξ i‖)) volume :=
      Filter.Eventually.of_forall fun s =>
        (by fun_prop :
            AEStronglyMeasurable (fun ξ : ES =>
              |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) -
                  Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))|) volume)
          |>.mul ((ha i).aestronglyMeasurable)
    simpa using tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ES => (0 : ℝ)) (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖) hmeas hbnd (ha i) hlim
  have hconv : (fun s : ℝ => normXm1 (fun ξ : ES =>
      heatVec νR s a ξ i - heatVec νR t₀ a ξ i)) =ᶠ[l]
      fun s : ℝ => ∫ ξ : ES,
        |Real.exp (-((νR * ‖ξ‖ ^ 2 * s))) - Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)))| *
          (‖ξ‖⁻¹ * ‖a ξ i‖) := by
    filter_upwards [] with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    show ‖ξ‖⁻¹ * ‖heatVec νR s a ξ i - heatVec νR t₀ a ξ i‖ = _
    rw [show heatVec νR s a ξ i =
        ((Real.exp (-((νR * ‖ξ‖ ^ 2 * s)) : ℝ) : ℂ) * a ξ i) from rfl,
      show heatVec νR t₀ a ξ i =
        ((Real.exp (-((νR * ‖ξ‖ ^ 2 * t₀)) : ℝ) : ℂ) * a ξ i) from rfl]
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  exact hmain.congr' hconv.symm

/-- The causal-truncation majorant of a Duhamel difference, integrated over
the horizon product measure.  Pointwise a.e. in `ξ` the weighted Duhamel
difference is bounded by the fiber integral of the joint majorant `G`; this
lemma packages that fiber bound plus the Fubini step.  The fiber proof is:
each Duhamel section `∫ r in Icc 0 t, K r` rewrites (via
`integral_Icc_eq_horizon_indicator`) to the horizon indicator integral
`∫ r, (if r ≤ t then K r else 0) ∂μT`; subtracting under one integral and
applying `norm_integral_le_integral_norm` then the pointwise
indicator-difference identity gives the fiber bound, and the ξ-integral of
the fiber bound is the product integral of `G` over `Λ = volume.prod μT`. -/
private theorem normXm1_duhamelDiff_le (ν : ℝ≥0) (hν : 0 < ν) (T t₀ s : ℝ)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T)
    (u : ℝ → ES → ComplexSpace) (i : Fin 3)
    (hjointT : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hsrcT : Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
        ‖continuousNavierSource u u p.2 p.1 i‖) (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    normXm1 (fun ξ : ES =>
        continuousDuhamel (ν : ℝ) u u s ξ i - continuousDuhamel (ν : ℝ) u u t₀ ξ i) ≤
      ∫ p : ES × ℝ,
        |(if p.2 ≤ s
            then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2)))
            else 0) -
            if p.2 ≤ t₀ then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))) else 0| *
          (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖)
        ∂(volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  let μT : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let Λ : Measure (ES × ℝ) := volume.prod μT
  let νR : ℝ := (ν : ℝ)
  have hνR : 0 < νR := by exact_mod_cast hν
  have hcoordT : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) Λ :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 T hjointT i
  let G : ES × ℝ → ℝ := fun p =>
    |(if p.2 ≤ s then Real.exp (-((νR * ‖p.1‖ ^ 2 * (s - p.2)))) else 0) -
        if p.2 ≤ t₀ then Real.exp (-((νR * ‖p.1‖ ^ 2 * (t₀ - p.2)))) else 0| *
      (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖)
  have hGnn : ∀ p, 0 ≤ G p := fun p =>
    mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  have hGaes : AEStronglyMeasurable G Λ :=
    (Measurable.abs (Measurable.sub
        (Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const)
        (Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const))).aestronglyMeasurable
      |>.mul ((by fun_prop : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹) Λ).mul
        (hcoordT.norm))
  have hGint : Integrable G Λ := by
    refine hsrcT.mono' hGaes (ae_of_all _ fun p => ?_)
    show ‖G p‖ ≤ ‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnn p)]
    have h1 : (if p.2 ≤ s then Real.exp (-((νR * ‖p.1‖ ^ 2 * (s - p.2)))) else 0) ≤ 1 := by
      by_cases h : p.2 ≤ s
      · rw [ite_eq_left h]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr h)))
      · rw [ite_eq_right h]; exact zero_le_one
    have h1n : 0 ≤ (if p.2 ≤ s then Real.exp (-((νR * ‖p.1‖ ^ 2 * (s - p.2)))) else 0) := by
      by_cases h : p.2 ≤ s
      · rw [ite_eq_left h]; exact (Real.exp_pos _).le
      · rw [ite_eq_right h]
    have h2 : (if p.2 ≤ t₀ then Real.exp (-((νR * ‖p.1‖ ^ 2 * (t₀ - p.2)))) else 0) ≤ 1 := by
      by_cases h : p.2 ≤ t₀
      · rw [ite_eq_left h]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr h)))
      · rw [ite_eq_right h]; exact zero_le_one
    have h2n : 0 ≤ (if p.2 ≤ t₀ then Real.exp (-((νR * ‖p.1‖ ^ 2 * (t₀ - p.2)))) else 0) := by
      by_cases h : p.2 ≤ t₀
      · rw [ite_eq_left h]; exact (Real.exp_pos _).le
      · rw [ite_eq_right h]
    have hsc : |(if p.2 ≤ s then Real.exp (-((νR * ‖p.1‖ ^ 2 * (s - p.2)))) else 0) -
        if p.2 ≤ t₀ then Real.exp (-((νR * ‖p.1‖ ^ 2 * (t₀ - p.2)))) else 0| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    have hb : 0 ≤ ‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    have heq : G p =
        |(if p.2 ≤ s then Real.exp (-((νR * ‖p.1‖ ^ 2 * (s - p.2)))) else 0) -
            if p.2 ≤ t₀ then Real.exp (-((νR * ‖p.1‖ ^ 2 * (t₀ - p.2)))) else 0| *
          (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖) := rfl
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hsc hb).trans (one_mul _).le
  have hle' : ∀ᵐ ξ ∂volume, ‖ξ‖⁻¹ *
      ‖continuousDuhamel νR u u s ξ i - continuousDuhamel νR u u t₀ ξ i‖ ≤
      ∫ r, G (ξ, r) ∂μT := by
    have hne : ∀ᵐ ξ ∂volume, (ξ : ES) ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne, hsrcT.prod_right_ae, hcoordT.prodMk_left] with ξ hξ0 hq hqaes
    -- Fiber data: `ξ ≠ 0`, the weighted source is integrable along the fiber
    -- and the source coordinate is a.e.-measurable along the fiber.
    let E : ℝ → ℝ → ℂ := fun t r =>
      if r ≤ t then ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ) *
        continuousNavierSource u u r ξ i else 0
    have hEp (t r : ℝ) (h : r ≤ t) : E t r =
        ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ) * continuousNavierSource u u r ξ i :=
      ite_eq_left h
    have hEn (t r : ℝ) (h : ¬ r ≤ t) : E t r = 0 := ite_eq_right h
    have hnrm_src : Integrable (fun r : ℝ => ‖continuousNavierSource u u r ξ i‖) μT := by
      have hmul :
          Integrable (fun r : ℝ => ‖ξ‖⁻¹ * ‖continuousNavierSource u u r ξ i‖) μT := hq
      refine (hmul.const_mul ‖(ξ : ES)‖).congr (ae_of_all _ fun r => ?_)
      show ‖(ξ : ES)‖ * (‖(ξ : ES)‖⁻¹ * ‖continuousNavierSource u u r ξ i‖) =
        ‖continuousNavierSource u u r ξ i‖
      rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ0), one_mul]
    have hsrc_int : Integrable (fun r : ℝ => continuousNavierSource u u r ξ i) μT :=
      ⟨hqaes,
        (hasFiniteIntegral_norm_iff (fun r : ℝ => continuousNavierSource u u r ξ i)).mp
          hnrm_src.hasFiniteIntegral⟩
    have hite_aes (t : ℝ) : AEStronglyMeasurable (E t) μT := by
      have hprod : AEStronglyMeasurable (fun r : ℝ =>
          ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ) *
            continuousNavierSource u u r ξ i) μT :=
        ((by fun_prop :
            Continuous (fun r : ℝ =>
              ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ))).aestronglyMeasurable).mul hqaes
      have hset : (E t : ℝ → ℂ) = Set.indicator (Iic t)
          (fun r : ℝ => ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ) *
            continuousNavierSource u u r ξ i) := by
        funext r
        rw [Set.indicator_apply]
        exact ite_congr (propext Set.mem_Iic).symm (fun _ => rfl) (fun _ => rfl)
      rw [hset]
      exact hprod.indicator isClosed_Iic.measurableSet
    have hite_int (t : ℝ) : Integrable (E t) μT :=
      hsrc_int.mono (hite_aes t) (ae_of_all _ fun r => by
        by_cases h : r ≤ t
        · rw [hEp t r h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt (Real.exp_pos _))]
          have : Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) ≤ 1 :=
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr
              (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr h)))
          exact (mul_le_mul_of_nonneg_right this (norm_nonneg _)).trans (one_mul _).le
        · rw [hEn t r h]
          simp)
    have hI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        continuousDuhamel νR u u t ξ i = ∫ r : ℝ, E t r ∂μT := by
      show ∫ r in Icc (0 : ℝ) t,
          ((Real.exp (-((νR * ‖ξ‖ ^ 2 * (t - r)))) : ℝ) : ℂ) *
            continuousNavierSource u u r ξ i = _
      rw [integral_Icc_eq_horizon_indicator t T ht]
    have hsub : continuousDuhamel νR u u s ξ i - continuousDuhamel νR u u t₀ ξ i =
        ∫ r : ℝ, E s r - E t₀ r ∂μT := by
      rw [hI s hs, hI t₀ ht₀, ← integral_sub (hite_int s) (hite_int t₀)]
    have hpoint (r : ℝ) : ‖ξ‖⁻¹ * ‖E s r - E t₀ r‖ = G (ξ, r) := by
      have hG : G (ξ, r) =
          |(if r ≤ s then Real.exp (-((νR * ‖ξ‖ ^ 2 * (s - r)))) else 0) -
              if r ≤ t₀ then Real.exp (-((νR * ‖ξ‖ ^ 2 * (t₀ - r)))) else 0| *
            (‖ξ‖⁻¹ * ‖continuousNavierSource u u r ξ i‖) := rfl
      rw [hG]
      by_cases h1 : r ≤ s <;> by_cases h2 : r ≤ t₀
      · rw [hEp s r h1, hEp t₀ r h2, ite_eq_left h1, ite_eq_left h2, ← sub_mul,
          ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        ring
      · rw [hEp s r h1, hEn t₀ r h2, ite_eq_left h1, ite_eq_right h2, sub_zero, sub_zero,
          norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        ring
      · rw [hEn s r h1, hEp t₀ r h2, ite_eq_right h1, ite_eq_left h2, zero_sub, zero_sub,
          norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
          abs_of_pos (Real.exp_pos _)]
        ring
      · rw [hEn s r h1, hEn t₀ r h2, ite_eq_right h1, ite_eq_right h2]
        simp
    calc ‖ξ‖⁻¹ * ‖continuousDuhamel νR u u s ξ i - continuousDuhamel νR u u t₀ ξ i‖
        = ‖ξ‖⁻¹ * ‖∫ r : ℝ, E s r - E t₀ r ∂μT‖ :=
          congrArg (fun x => ‖ξ‖⁻¹ * ‖x‖) hsub
      _ ≤ ‖ξ‖⁻¹ * ∫ r : ℝ, ‖E s r - E t₀ r‖ ∂μT :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
            (inv_nonneg.mpr (norm_nonneg ξ))
      _ = ∫ r : ℝ, ‖ξ‖⁻¹ * ‖E s r - E t₀ r‖ ∂μT :=
          (integral_smul ‖(ξ : ES)‖⁻¹ fun r => ‖E s r - E t₀ r‖).symm
      _ = ∫ r : ℝ, G (ξ, r) ∂μT := integral_congr_ae (ae_of_all _ hpoint)
  have hprod_int : Integrable (fun ξ : ES => ∫ r, G (ξ, r) ∂μT) volume :=
    (hGint.integral_norm_prod_left).congr (ae_of_all _ fun ξ =>
      integral_congr_ae (ae_of_all _ fun r =>
        (Real.norm_eq_abs _).trans (abs_of_nonneg (hGnn _))))
  calc normXm1 (fun ξ : ES =>
          continuousDuhamel (ν : ℝ) u u s ξ i - continuousDuhamel (ν : ℝ) u u t₀ ξ i)
      = ∫ ξ : ES, ‖ξ‖⁻¹ * ‖continuousDuhamel νR u u s ξ i - continuousDuhamel νR u u t₀ ξ i‖
          ∂volume := rfl
    _ ≤ ∫ ξ : ES, ∫ r : ℝ, G (ξ, r) ∂μT ∂volume :=
          integral_mono_of_nonneg (ae_of_all _ fun ξ =>
            mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hprod_int hle'
    _ = ∫ p : ES × ℝ, G p ∂Λ := (integral_prod G hGint).symm

/-- The coordinate `X⁻¹` weight of the free heat term is integrable for
`t ≥ 0`: the heat multiplier is `∈ (0,1]` there, so it is dominated
pointwise by the datum's weighted integrability. -/
private theorem heatVec_xm1Integrable (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (νR t : ℝ) (hνR : 0 < νR) (ht : 0 ≤ t) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatVec νR t a ξ i‖) := by
  have hpe (ξ : ES) : ‖ξ‖⁻¹ * ‖heatVec νR t a ξ i‖ =
      Real.exp (-((νR * ‖ξ‖ ^ 2 * t))) * (‖ξ‖⁻¹ * ‖a ξ i‖) := by
    show ‖ξ‖⁻¹ * ‖((Real.exp (-((νR * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * a ξ i)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    ring
  have hexp_le (ξ : ES) : Real.exp (-((νR * ‖ξ‖ ^ 2 * t))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) ht))
  refine (ha i).mono'
    ((by fun_prop : AEStronglyMeasurable
        (fun ξ : ES => ‖ξ‖⁻¹) volume).mul
      ((by fun_prop :
          AEStronglyMeasurable (fun ξ : ES => ((Real.exp (-((νR * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)))
            volume)
        |>.mul (haM i)).norm) ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)), hpe ξ]
  exact mul_le_of_le_one_left (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (hexp_le ξ)

/-- The `X⁻¹`-weighted Duhamel coordinate is integrable on the horizon: the
Duhamel term is the mild image (leaf 2b) minus the heat term, and
`xm1_integrable_diff` discharges the coordinate weight. -/
private theorem continuousDuhamel_xm1Integrable (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (hmM : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, AEStronglyMeasurable
        (fun ξ : ES => mildImage ν hν a v t ξ i) volume)
    (hmXm1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖mildImage ν hν a v t ξ i‖))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel (ν : ℝ) v v t ξ i‖) := by
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hfield : (fun ξ : ES => continuousDuhamel (ν : ℝ) v v t ξ)
      = fun ξ : ES => mildImage ν hν a v t ξ - heatVec (ν : ℝ) t a ξ := by
    ext ξ j
    show continuousDuhamel (ν : ℝ) v v t ξ j =
        mildImage ν hν a v t ξ j - heatVec (ν : ℝ) t a ξ j
    rw [show mildImage ν hν a v t ξ j =
        heatVec (ν : ℝ) t a ξ j + continuousDuhamel (ν : ℝ) v v t ξ j from rfl]
    abel
  refine (xm1_integrable_diff (fun ξ : ES => mildImage ν hν a v t ξ)
      (fun ξ : ES => heatVec (ν : ℝ) t a ξ) (hmM t ht)
      (fun j =>
        (by fun_prop :
            AEStronglyMeasurable
              (fun ξ : ES => ((Real.exp (-(((ν : ℝ) * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ))) volume)
          |>.mul (haM j))
      (hmXm1 t ht) (heatVec_xm1Integrable a haM ha (ν : ℝ) t hνR ht.1) i).congr
    (ae_of_all _ fun ξ =>
      (congrArg (fun y : ComplexSpace => ‖ξ‖⁻¹ * ‖y i‖) (congrFun hfield ξ)).symm)

/-- The coordinate Duhamel difference tends to `0` in the `X⁻¹`-weighted mass
along the horizon.  Squeezed between `0` and the product-measure majorant of
`normXm1_duhamelDiff_le`; that majorant integral tends to `0` by dominated
convergence on `Λ = volume.prod (volume.restrict (Icc 0 T))` against the
joint weighted source: pointwise the causal-truncation difference goes to
`0` off the null fiber `p.2 = t₀` (it is `≤ 1` there because every heat
multiplier factor lies in `[0,1]`). -/
private theorem tendsto_normXm1_duhamelDiff (ν : ℝ≥0) (hν : 0 < ν) (T t₀ : ℝ)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (v : ℝ → ES → ComplexSpace)
    (hjointT : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource v v p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hsrcT : ∀ i : Fin 3, Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
        ‖continuousNavierSource v v p.2 p.1 i‖)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (i : Fin 3) :
    Tendsto (fun s : ℝ => normXm1 (fun ξ : ES =>
        continuousDuhamel (ν : ℝ) v v s ξ i - continuousDuhamel (ν : ℝ) v v t₀ ξ i))
      (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 0) := by
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  let μT : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let Λ : Measure (ES × ℝ) := volume.prod μT
  let l := 𝓝[Icc (0 : ℝ) T] t₀
  let Gs : ℝ → ES × ℝ → ℝ := fun s p =>
    |(if p.2 ≤ s
        then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2)))
        else 0) -
        if p.2 ≤ t₀ then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))) else 0| *
      (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)
  have hcoordT : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource v v p.2 p.1 i) Λ :=
    continuousNavierSource_coord_aestronglyMeasurable v v 0 T hjointT i
  have hGmeas : ∀ s : ℝ, AEStronglyMeasurable (Gs s) Λ := fun s =>
    (Measurable.abs (Measurable.sub
        (Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const)
        (Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const))).aestronglyMeasurable
      |>.mul ((by fun_prop : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹) Λ).mul
        hcoordT.norm)
  have hGnn : ∀ s p, 0 ≤ Gs s p := fun s p =>
    mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  have hae_snd : ∀ᵐ p ∂Λ, p.2 ≠ t₀ := by
    have h1 : μT {t₀} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton t₀)]
      exact measure_mono_null inter_subset_left Real.volume_singleton
    have hnull : Λ {p : ES × ℝ | p.2 = t₀} = 0 := by
      have hset : {p : ES × ℝ | p.2 = t₀} = Set.univ ×ˢ ({t₀} : Set ℝ) := by
        ext p; simp
      rw [hset, Measure.prod_prod, h1, mul_zero]
    rw [ae_iff]
    have hset : {p : ES × ℝ | ¬p.2 ≠ t₀} = {p | p.2 = t₀} := by ext p; simp
    rw [hset]
    exact hnull
  have hlim : ∀ᵐ p ∂Λ, Tendsto (fun s : ℝ => Gs s p) l (𝓝 0) := by
    refine hae_snd.mono ?_
    intro p hp
    rcases lt_or_gt_of_ne hp with h | h
    · have hev : ∀ᶠ s in l, p.2 < s := nhdsWithin_le_nhds (lt_mem_nhds h)
      have hkey : Tendsto (fun s : ℝ =>
          |Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) -
              Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))| *
            (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)) l (𝓝 0) := by
        have hg : Tendsto (fun s : ℝ => -((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) l
            (𝓝 (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))) :=
          ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto t₀).neg.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun s : ℝ =>
            Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) -
              Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))) l
            (𝓝 (Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))) -
              Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))))) :=
          ((Real.continuous_exp.continuousAt.tendsto).comp hg).sub tendsto_const_nhds
        rw [sub_self] at h2
        simpa using (h2.abs).mul tendsto_const_nhds
      have heq : (fun s : ℝ =>
          |Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) -
              Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))| *
            (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)) =ᶠ[l]
          fun s : ℝ => Gs s p := by
        filter_upwards [hev] with s hs
        show |Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) -
            Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))| *
            (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖) =
          |((if p.2 ≤ s then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) else 0) -
              if p.2 ≤ t₀ then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))) else 0)| *
            (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)
        rw [ite_eq_left (le_of_lt hs), ite_eq_left (le_of_lt h)]
      exact hkey.congr' heq
    · have hev : ∀ᶠ s in l, s < p.2 := nhdsWithin_le_nhds (Iio_mem_nhds h)
      have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[l] fun s : ℝ => Gs s p := by
        filter_upwards [hev] with s hlt
        show (0 : ℝ) =
          |((if p.2 ≤ s then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2))) else 0) -
              if p.2 ≤ t₀ then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2))) else 0)| *
            (‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)
        rw [ite_eq_right (fun hh => lt_irrefl _ (lt_of_lt_of_le hlt hh)),
          ite_eq_right (fun hh => lt_irrefl _ (lt_of_lt_of_le h hh))]
        simp
      exact tendsto_const_nhds.congr' heq
  have hmeas : ∀ᶠ s in l, AEStronglyMeasurable (Gs s) Λ :=
    Filter.Eventually.of_forall hGmeas
  have hbnd : ∀ᶠ s in l, ∀ᵐ p ∂Λ, ‖Gs s p‖ ≤
      ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖ :=
    Filter.Eventually.of_forall fun s => ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (hGnn s p)]
      have hA : 0 ≤ (if p.2 ≤ s
          then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2)))
          else 0) ∧ (if p.2 ≤ s
          then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (s - p.2)))
          else 0) ≤ 1 := by
        rcases em (p.2 ≤ s) with h | h
        · rw [ite_eq_left h]
          exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
            (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr h)))⟩
        · rw [ite_eq_right h]
          exact ⟨le_refl 0, zero_le_one⟩
      have hB : 0 ≤ (if p.2 ≤ t₀
          then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))
          else 0) ∧ (if p.2 ≤ t₀
          then Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t₀ - p.2)))
          else 0) ≤ 1 := by
        rcases em (p.2 ≤ t₀) with h | h
        · rw [ite_eq_left h]
          exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
            (mul_nonneg (mul_nonneg hνR.le (sq_nonneg _)) (sub_nonneg.mpr h)))⟩
        · rw [ite_eq_right h]
          exact ⟨le_refl 0, zero_le_one⟩
      obtain ⟨hA0, hA1⟩ := hA
      obtain ⟨hB0, hB1⟩ := hB
      refine (mul_le_mul_of_nonneg_right ?_
        (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))).trans (one_mul _).le
      rw [abs_le]
      constructor <;> nlinarith
  have hmain : Tendsto (fun s : ℝ => ∫ p : ES × ℝ, Gs s p ∂Λ) l (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ES × ℝ => (0 : ℝ))
      (fun p : ES × ℝ => ‖p.1‖⁻¹ * ‖continuousNavierSource v v p.2 p.1 i‖)
      hmeas hbnd (hsrcT i) hlim
  have hlower : ∀ᶠ s in l, (0 : ℝ) ≤ normXm1 (fun ξ : ES =>
      continuousDuhamel (ν : ℝ) v v s ξ i - continuousDuhamel (ν : ℝ) v v t₀ ξ i) :=
    Filter.Eventually.of_forall fun s => by
      unfold normXm1
      exact integral_nonneg fun ξ =>
        mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) l (𝓝 0)) hmain hlower ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact normXm1_duhamelDiff_le ν hν T t₀ s ht₀ hs v i hjointT (hsrcT i)

/-- **Leaf 2d bootstrap** for general horizon data: the `X⁻¹`-valued time
section `t ↦ toXm1Spatial (mild image at t)` of the horizon-truncated mild
image is strongly measurable.  The derivation is a *continuity* statement,
not a measurability construction: at `t₀ ∈ Icc 0 T` the section difference
is one `toXm1Spatial` of the pointwise field difference
(`toXm1Spatial_congr_raw` glues `mildImageIcc` to `mildImage` on the
horizon, `toXm1Spatial_sub` moves the subtraction inside the quotient), its
norm is `coordinateXm1Mass` of that difference (`norm_toXm1Spatial`), the
mass splits by `coordinateXm1Mass_add_le` into the heat and Duhamel parts,
the heat part goes to `0` coordinatewise by `tendsto_normXm1_heatVec_sub`
and the Duhamel part by `tendsto_normXm1_duhamelDiff`; `tendsto_finsetSum`
sums the coordinate bounds and the squeeze theorem gives
`ContinuousOn`, whence `ContinuousOn.aestronglyMeasurable`
(no `Lp` separability is needed — `ℝ` is second countable). -/
theorem mildTimeLeaf_hmXm1Time (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (hmM : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, AEStronglyMeasurable
        (fun ξ : ES => mildImage ν hν a v t ξ i) volume)
    (hmXm1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ i, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖mildImage ν hν a v t ξ i‖))
    (hjointT : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource v v p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hsrcT : ∀ i : Fin 3, Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
        ‖continuousNavierSource v v p.2 p.1 i‖)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    AEStronglyMeasurable
      (xm1Section (mildImageIcc ν hν T a v)
        (mildImageIcc_aestronglyMeasurable ν hν T a v hmM)
        (mildImageIcc_integrableXm1 ν hν T a v hmXm1))
      (leiLinTimeMeasure T) := by
  let Φ : ℝ → Xm1Spatial := fun t =>
    xm1Section (mildImageIcc ν hν T a v)
      (mildImageIcc_aestronglyMeasurable ν hν T a v hmM)
      (mildImageIcc_integrableXm1 ν hν T a v hmXm1) t
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hheatAES : ∀ (t : ℝ), 0 ≤ t → ∀ j : Fin 3,
      AEStronglyMeasurable (fun ξ : ES => heatVec (ν : ℝ) t a ξ j) volume :=
    fun t ht j =>
      (by fun_prop :
          AEStronglyMeasurable
            (fun ξ : ES => ((Real.exp (-(((ν : ℝ) * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ))) volume)
        |>.mul (haM j)
  have hΦ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Φ t =
      toXm1Spatial (fun ξ : ES => mildImage ν hν a v t ξ) (fun i => hmM t ht i)
        (fun i => hmXm1 t ht i) :=
    toXm1Spatial_congr_raw (fun i => mildImageIcc_aestronglyMeasurable ν hν T a v hmM t i)
      (fun i => hmM t ht i) (fun i => mildImageIcc_integrableXm1 ν hν T a v hmXm1 t i)
      (fun i => hmXm1 t ht i) (fun ξ => mildImageIcc_of_mem ν hν T a v t ht ξ)
  have hcont : ContinuousOn Φ (Icc (0 : ℝ) T) := fun t₀ ht₀ =>
    tendsto_iff_dist_tendsto_zero.mpr (by
      have hbound : Tendsto (fun s : ℝ => ∑ i : Fin 3,
          (normXm1 (fun ξ : ES =>
              heatVec (ν : ℝ) s a ξ i - heatVec (ν : ℝ) t₀ a ξ i) +
              normXm1 (fun ξ : ES =>
                continuousDuhamel (ν : ℝ) v v s ξ i -
                  continuousDuhamel (ν : ℝ) v v t₀ ξ i)))
          (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 0) := by
        simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 3))
          (fun i _ => (tendsto_normXm1_heatVec_sub a ha (ν : ℝ) hνR T t₀ ht₀ i).add
            (tendsto_normXm1_duhamelDiff ν hν T t₀ ht₀ v hjointT hsrcT i))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 0))
        hbound (Filter.Eventually.of_forall fun s => dist_nonneg) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hdecomp : (fun ξ : ES => mildImage ν hν a v s ξ - mildImage ν hν a v t₀ ξ) =
          (fun ξ : ES => heatVec (ν : ℝ) s a ξ - heatVec (ν : ℝ) t₀ a ξ) +
            fun ξ : ES =>
              continuousDuhamel (ν : ℝ) v v s ξ - continuousDuhamel (ν : ℝ) v v t₀ ξ := by
        ext ξ j
        show mildImage ν hν a v s ξ j - mildImage ν hν a v t₀ ξ j =
            heatVec (ν : ℝ) s a ξ j - heatVec (ν : ℝ) t₀ a ξ j +
              (continuousDuhamel (ν : ℝ) v v s ξ j - continuousDuhamel (ν : ℝ) v v t₀ ξ j)
        rw [show mildImage ν hν a v s ξ j =
              heatVec (ν : ℝ) s a ξ j + continuousDuhamel (ν : ℝ) v v s ξ j from rfl,
          show mildImage ν hν a v t₀ ξ j =
              heatVec (ν : ℝ) t₀ a ξ j + continuousDuhamel (ν : ℝ) v v t₀ ξ j from rfl]
        abel
      calc dist (Φ s) (Φ t₀)
          = ‖Φ s - Φ t₀‖ := dist_eq_norm _ _
        _ = ‖toXm1Spatial
              (fun ξ : ES => mildImage ν hν a v s ξ - mildImage ν hν a v t₀ ξ)
              (fun i => (hmM s hs i).sub (hmM t₀ ht₀ i))
              (fun i => xm1_integrable_diff (fun ξ : ES => mildImage ν hν a v s ξ)
                (fun ξ : ES => mildImage ν hν a v t₀ ξ) (hmM s hs) (hmM t₀ ht₀)
                (hmXm1 s hs) (hmXm1 t₀ ht₀) i)‖ := by
              rw [hΦ s hs, hΦ t₀ ht₀,
                toXm1Spatial_sub (fun ξ : ES => mildImage ν hν a v s ξ)
                  (fun ξ : ES => mildImage ν hν a v t₀ ξ) (hmM s hs) (hmM t₀ ht₀)
                  (hmXm1 s hs) (hmXm1 t₀ ht₀)]
        _ = coordinateXm1Mass
              (fun ξ : ES => mildImage ν hν a v s ξ - mildImage ν hν a v t₀ ξ) :=
              norm_toXm1Spatial
                (fun ξ : ES => mildImage ν hν a v s ξ - mildImage ν hν a v t₀ ξ)
                (fun i => (hmM s hs i).sub (hmM t₀ ht₀ i))
                (fun i => xm1_integrable_diff (fun ξ : ES => mildImage ν hν a v s ξ)
                  (fun ξ : ES => mildImage ν hν a v t₀ ξ) (hmM s hs) (hmM t₀ ht₀)
                  (hmXm1 s hs) (hmXm1 t₀ ht₀) i)
        _ ≤ coordinateXm1Mass (fun ξ : ES =>
                heatVec (ν : ℝ) s a ξ - heatVec (ν : ℝ) t₀ a ξ)
            + coordinateXm1Mass (fun ξ : ES =>
                continuousDuhamel (ν : ℝ) v v s ξ - continuousDuhamel (ν : ℝ) v v t₀ ξ) := by
              rw [hdecomp]
              convert coordinateXm1Mass_add_le
                (fun ξ : ES => heatVec (ν : ℝ) s a ξ - heatVec (ν : ℝ) t₀ a ξ)
                (fun ξ : ES =>
                  continuousDuhamel (ν : ℝ) v v s ξ - continuousDuhamel (ν : ℝ) v v t₀ ξ)
                (fun i => xm1_integrable_diff (fun ξ : ES => heatVec (ν : ℝ) s a ξ)
                  (fun ξ : ES => heatVec (ν : ℝ) t₀ a ξ) (hheatAES s hs.1) (hheatAES t₀ ht₀.1)
                  (heatVec_xm1Integrable a haM ha (ν : ℝ) s hνR hs.1)
                  (heatVec_xm1Integrable a haM ha (ν : ℝ) t₀ hνR ht₀.1) i)
                (fun i => xm1_integrable_diff
                  (fun ξ : ES => continuousDuhamel (ν : ℝ) v v s ξ)
                  (fun ξ : ES => continuousDuhamel (ν : ℝ) v v t₀ ξ)
                  (fun j => ((hmM s hs j).sub (hheatAES s hs.1 j)).congr
                    (ae_of_all volume fun ξ => by
                      show mildImage ν hν a v s ξ j - heatVec (ν : ℝ) s a ξ j =
                          continuousDuhamel (ν : ℝ) v v s ξ j
                      rw [show mildImage ν hν a v s ξ j =
                            heatVec (ν : ℝ) s a ξ j + continuousDuhamel (ν : ℝ) v v s ξ j
                            from rfl]
                      abel))
                  (fun j => ((hmM t₀ ht₀ j).sub (hheatAES t₀ ht₀.1 j)).congr
                    (ae_of_all volume fun ξ => by
                      show mildImage ν hν a v t₀ ξ j - heatVec (ν : ℝ) t₀ a ξ j =
                          continuousDuhamel (ν : ℝ) v v t₀ ξ j
                      rw [show mildImage ν hν a v t₀ ξ j =
                            heatVec (ν : ℝ) t₀ a ξ j + continuousDuhamel (ν : ℝ) v v t₀ ξ j
                            from rfl]
                      abel))
                  (continuousDuhamel_xm1Integrable ν hν T a v haM ha hmM hmXm1 s hs)
                  (continuousDuhamel_xm1Integrable ν hν T a v haM ha hmM hmXm1 t₀ ht₀) i)
                (fun i => (xm1_integrable_diff (fun ξ : ES => mildImage ν hν a v s ξ)
                    (fun ξ : ES => mildImage ν hν a v t₀ ξ) (hmM s hs) (hmM t₀ ht₀)
                    (hmXm1 s hs) (hmXm1 t₀ ht₀) i).congr
                  (ae_of_all volume fun ξ =>
                    congrArg (fun y : ℂ => ‖ξ‖⁻¹ * ‖y‖) (congrFun (congrFun hdecomp ξ) i)))
              using 1
              · rfl
          _ = ∑ i : Fin 3, (normXm1 (fun ξ : ES =>
                  heatVec (ν : ℝ) s a ξ i - heatVec (ν : ℝ) t₀ a ξ i) +
                normXm1 (fun ξ : ES =>
                  continuousDuhamel (ν : ℝ) v v s ξ i -
                    continuousDuhamel (ν : ℝ) v v t₀ ξ i)) := by
              simp only [coordinateXm1Mass, Finset.sum_add_distrib, Pi.sub_apply])
  exact (hcont.aestronglyMeasurable (μ := volume) isClosed_Icc.measurableSet)

/-- Leaf 2d for general boxes: the `X⁻¹`-valued time section of the
horizon-truncated mild image of an actual box element is strongly
measurable.  With the S3 leaves `mildTimeLeaf_hmM`, `mildTimeLeaf_hmXm1`
and the joint-source suppliers this is exactly the record field
`hmXm1Time` for general box elements — derived from the continuity of the
section map, not postulated. -/
theorem mildTimeLeaf_hmXm1Time_actualBox (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖)) :
    ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (xm1Section (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
          (mildImageIcc_aestronglyMeasurable ν hν T a
            (everywhereRawRepresentative ν T x.1) (mildTimeLeaf_hmM ν hν T R a haM x))
          (mildImageIcc_integrableXm1 ν hν T a
            (everywhereRawRepresentative ν T x.1) (mildTimeLeaf_hmXm1 ν hν T R a haM ha x)))
        (leiLinTimeMeasure T) := fun x =>
  mildTimeLeaf_hmXm1Time ν hν T a (everywhereRawRepresentative ν T x.1) haM ha
    (mildTimeLeaf_hmM ν hν T R a haM x)
    (mildTimeLeaf_hmXm1 ν hν T R a haM ha x)
    (mildLeafHjointDiag ν hν T R x)
    (fun i => integrable_weightedContinuousNavierSource_coord_of_actualBox ν hν T (2 * R) (2 * R)
      x T ⟨hT, le_refl T⟩ (mildLeafHjointDiag ν hν T R x) i)

/-!

The two record fields left open by S3 for *general* box elements are named
here precisely:

1. `hmX1` at **every** horizon time.  `mildTimeLeaf_hmX1_ae` derives the
   `volume.restrict (Icc 0 T)`-a.e. reading, and `D₃` maximal regularity
   (`continuousDuhamel_X1_integrability`, whose second conclusion is
   `hprod.prod_left_ae`) cannot in general upgrade `a.e.` to `∀ t`: a
   pointwise `X¹` bound for the Duhamel part at time `t` needs
   `∫ s in Icc 0 t, τ (s)^{-1/2} ‖ξ‖-weighted` source mass finite for *that*
   `t`, i.e. membership of the weighted source in `L¹_t` on every initial
   interval, which the box `L²`-based weights do not supply
   (`s^{-1/2} ∈ L¹(0,T) \ L²(0,T)`).  Exact residual:
   `∀ x t ∈ Icc 0 T, ∀ i, Integrable (fun ξ => ‖ξ‖ * ‖mildImage ν hν a (rep x) t ξ i‖)`.
2. `hmX1Time` (2e): strong measurability (into the `Lp`-space valued
   section function `viscousX1Section`) of the horizon-truncated mild image
   for general boxes.  Leaf 2d (`hmXm1Time`, the `Xm1Spatial`-valued
   section) is NO LONGER open: `mildTimeLeaf_hmXm1Time_actualBox` derives
   it in this module — the section is *continuous* on `[0, T]` in the
   quotient distance, by pointwise strong continuity of the heat flow in
   the `X⁻¹` mass (`tendsto_normXm1_heatVec_sub`) plus dominated
   convergence of the Duhamel difference majorant under `Λ` against the
   joint-weighted source: the `‖ξ‖⁻¹` weight leaves every heat integrand
   in `L¹(dξ)` at every horizon time, and the two kernel-difference
   weights `|ite(p.2 ≤ s) e^{−ν‖p.1‖²(s−p.2)} − ite(p.2 ≤ t₀)
   e^{−ν‖p.1‖²(t₀−p.2)}|` are bounded by `1` for all `s`, so no `L¹_t`
   source budget — and no `s^{−1/2}` smoothing singularity — enters.
   The `X¹`-valued section 2e has no analogous derivation: its
   constructor obligation is the field `hmX1` (leaf 2c) at every horizon
   time, and supplying that is exactly the `s^{−1/2} ∈ L¹(0,T) \ L²(0,T)`
   wall of item 1.  Exact residual: the `AEStronglyMeasurable` statement
   of `viscousX1Section` for general box elements, blocked at the
   surviving proposition of item 1 — not an `a.e.`-time restatement of
   the closed `xm1Section` reading.

Polarization leaves 3a/3b (step 4) remain premises: packaging
`continuousMildImage_sub_coordinateXm1Mass_le` /
`coordinateX1Mass_continuousMildImage_sub_le` at BanachContraction level
requires the *all-`ξ` pointwise* convolution-section integrabilities
(`∀ ξ j i s, Integrable (fun η => rep s η j * rep s (ξ - η) i)` etc.) that
`mildLeafHjointL/R` (a.e. joint measurability) does not supply, and the
identities are not junk-stable on the null set where they fail. -/

/-! ### Open boundary, as two named sub-records

The leaves `hmM`, `hmXm1`, `hmX1` of `MildAssemblyLeaves` quantify over
every *horizon* time `t ∈ Icc 0 T`; S3 above derives `hmM` (2a), `hmXm1`
(2b) and `hmX1Int` (2f) for every box element, the `a.e.`-time reading of
`hmX1` (2c) via `mildTimeLeaf_hmX1_ae`, and the `Xm1Spatial`-valued
section leaf `hmXm1Time` (2d) via
`mildTimeLeaf_hmXm1Time_actualBox` (continuity in the quotient distance;
see the obstruction record above).  What remains — the every-time `hmX1`
and the viscous section leaf `hmX1Time` (2e), whose constructor
obligation is the every-time `hmX1` — is packaged verbatim below.  An unrestricted `∀ t` reading of the moment leaves
is a FALSE premise — at `t < 0` they demand pointwise `X^{±1}` integrability
of the backward heat flow applied to an arbitrary admissible `a`; the heat
multiplier `exp(ν ‖ξ‖² t)` explodes there while `ha`/`ha1` supply only
polynomial control (structural witness: `a ξ i = exp(-‖ξ‖²)` at `ν = 1`,
`t = -1`).  The restriction is the faithful one: the completed slots read
time sections only `leiLinTimeMeasure T`-a.e., and the `∀ t` constructor
obligation of `xm1Section`/`viscousX1Section` is discharged definitionally
by the horizon truncation `mildImageIcc` and its promotion lemmas in
`Navier/Analysis/ContinuousLeiLinMildFixedPoint.lean`. -/

/-- The pointwise-in-time mild-image leaves: the six fields of
`MildAssemblyLeaves` that speak about individual times (spatial moment
integrability at every horizon time `t ∈ Icc 0 T`, the two time-section
measurabilities of the horizon-truncated mild image, and the time
integrability of its `X¹` mass).  For general box elements this module
derives `hmM` (2a), `hmXm1` (2b), `hmXm1Time` (2d,
`mildTimeLeaf_hmXm1Time_actualBox`) and `hmX1Int` (2f), and the `a.e.`
reading of `hmX1` (`mildTimeLeaf_hmX1_ae`); the every-time `hmX1` and
`hmX1Time` (2e) remain the exact open propositions behind the mild fixed
point constructor (see the obstruction record above). -/
structure MildAssemblyTimeLeaves
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R) where
  /-- Leaf 2a: spatial measurability of the mild image at every horizon time.
  Quantified over `t ∈ Icc 0 T` only: the backward heat multiplier
  `exp(ν ‖ξ‖² |t|)` destroys every `X^{±1}` moment at `t < 0` for a general
  admissible datum, so an unrestricted `∀ t` reading of this leaf is a false
  premise (structural witness: `a ξ i = exp(-‖ξ‖²)` at `ν = 1`, `t = -1`).
  The restriction WEAKENS the travelling premise; the horizon is exactly what
  the completed slots read. -/
  hmM : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      AEStronglyMeasurable (fun ξ : ES =>
        mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i) volume
  /-- Leaf 2b: `X⁻¹` integrability of the mild image at every horizon time
  (horizon-restricted for the same reason as leaf 2a). -/
  hmXm1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2c: `X¹` integrability of the mild image at every horizon time
  (horizon-restricted for the same reason as leaf 2a).  For general boxes
  only the `leiLinTimeMeasure T`-a.e. reading is derived
  (`mildTimeLeaf_hmX1_ae`); the every-time upgrade is the `s^{−1/2}` wall
  recorded above. -/
  hmX1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2d: strong measurability of the `X⁻¹`-valued time section of the
  horizon-truncated mild image.  Derived for general boxes in this module
  by `mildTimeLeaf_hmXm1Time_actualBox` — from continuity of the section
  in the quotient distance, not postulated. -/
  hmXm1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (xm1Section (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
          (mildImageIcc_aestronglyMeasurable ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmM x))
          (mildImageIcc_integrableXm1 ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmXm1 x)))
        (leiLinTimeMeasure T)
  /-- Leaf 2e: strong measurability of the viscous `X¹`-valued time section of
  the horizon-truncated mild image.  Open for general boxes: the section's
  `∀ t` constructor obligation is leaf 2c, so the surviving proposition is
  the every-time `hmX1` recorded above. -/
  hmX1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (viscousX1Section (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
          (mildImageIcc_aestronglyMeasurable ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmM x))
          (mildImageIcc_integrableX1 ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmX1 x)) ν)
        (leiLinTimeMeasure T)
  /-- Leaf 2f: time integrability of the horizon-truncated mild image's `X¹`
  mass. -/
  hmX1Int : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      Integrable (fun t : ℝ => coordinateX1Mass
        (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t))
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
#check @mildTimeLeaf_hmM
#print axioms mildTimeLeaf_hmM
#check @mildTimeLeaf_hmXm1
#print axioms mildTimeLeaf_hmXm1
#check @mildTimeLeaf_d3X1
#print axioms mildTimeLeaf_d3X1
#check @mildTimeLeaf_hmX1_ae
#print axioms mildTimeLeaf_hmX1_ae
#check @mildTimeLeaf_hmX1Int
#print axioms mildTimeLeaf_hmX1Int
#check @mildTimeLeaf_hmXm1Time
#print axioms mildTimeLeaf_hmXm1Time
#check @mildTimeLeaf_hmXm1Time_actualBox
#print axioms mildTimeLeaf_hmXm1Time_actualBox
#check @MildAssemblyTimeLeaves
#check @MildAssemblyTimeLeaves.mk
#print axioms MildAssemblyTimeLeaves.mk
#check @MildAssemblyPolarizationLeaves
#check @MildAssemblyPolarizationLeaves.mk
#print axioms MildAssemblyPolarizationLeaves.mk
#check @mildAssemblyLeaves_of_namedLeaves
#print axioms mildAssemblyLeaves_of_namedLeaves
#check @mildAssemblyTimeLeaves_of
#print axioms mildAssemblyTimeLeaves_of
#check @mildAssemblyPolarizationLeaves_of
#print axioms mildAssemblyPolarizationLeaves_of
end Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
