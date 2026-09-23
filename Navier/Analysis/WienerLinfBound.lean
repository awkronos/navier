import Navier.Analysis.WienerMoments
import Navier.Analysis.WienerMildGood
import Navier.Analysis.WienerPointwiseBridge

/-!
# Frequency-side `L∞` bound for the large-data Wiener solution

On the (slightly shorter) horizon `10⁶ T ‖a₀‖² ≤ ν`, the unique small-radius fixed
point `x` of the Wiener mild map keeps the essential bound of its datum: if every
coordinate of `a₀` is bounded by `A` almost everywhere, then so is every coordinate
of `x t`, up to the factor two.  Proof: the set of paths with that essential bound
is closed in `C([0,T], L¹)` and invariant under the Picard map (the Duhamel term is
bounded pointwise by `27 R ‖y‖ ∫ singWeight`), so the invariant-set Picard theorem
and uniqueness put the fixed point inside it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution

namespace Navier.Analysis.WienerLinfBound

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerPointwiseBridge
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerMoments

/-! ## The closed essential ball -/

/-- `L¹` classes with essential bound `R`. -/
def Zb (R : ℝ) : Set L1C := {f | ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ ≤ R}

theorem isClosed_Zb (R : ℝ) : IsClosed (Zb R) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  have hmeas : TendstoInMeasure (volume : Measure ES) (fun n => ⇑(u n)) atTop ⇑f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hlim
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂(volume : Measure ES), ∀ n, ‖u (ns n) ξ‖ ≤ R :=
    ae_all_iff.mpr fun n => hu (ns n)
  show ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ ≤ R
  filter_upwards [hns, hall] with ξ h1 h2
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp h1) h2

variable {ν T : ℝ}

/-- Paths all of whose coordinates are essentially bounded by `R`. -/
def linfSet (T R : ℝ) : Set C(Icc (0 : ℝ) T, V1) := {y | ∀ t i, y t i ∈ Zb R}

theorem isClosed_linfSet (R : ℝ) : IsClosed (linfSet T R) := by
  have h : linfSet T R = ⋂ t : Icc (0 : ℝ) T, ⋂ i : Fin 3,
      (fun y : C(Icc (0 : ℝ) T, V1) => y t i) ⁻¹' Zb R := by
    ext y; simp [linfSet]
  rw [h]
  exact isClosed_iInter fun t => isClosed_iInter fun i =>
    (isClosed_Zb R).preimage ((continuous_apply i).comp (continuous_eval_const t))

/-! ## The heat part -/

theorem heatOp_mem_Zb (hν : 0 ≤ ν) (t : ℝ) (a₀ : V1) {A : ℝ} (i : Fin 3)
    (ha : a₀ i ∈ Zb A) : heatOp ν t a₀ i ∈ Zb A := by
  show ∀ᵐ ξ ∂(volume : Measure ES), ‖(heatOp ν t a₀ i) ξ‖ ≤ A
  rw [heatOp_apply]
  filter_upwards [coeFn_mulL (heatLinf ν t) (a₀ i), coeFn_heatLinf hν t, ha] with ξ h1 h2 h3
  rw [h1, h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (heatFactor_nonneg _ _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (heatFactor_le_one hν (le_max_right _ _) ξ)).trans
    h3

/-! ## The Duhamel part -/

theorem heat_mul_norm_le {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ξ : ES) :
    heatFactor ν σ ξ * ‖ξ‖ ≤ singWeight ν σ := by
  rw [← sqrt_mul_inv_eq_singWeight hν hσ]
  unfold heatFactor
  have h := mul_exp_neg_sq_le (a := ν * σ) (r := ‖ξ‖) (by positivity) (norm_nonneg _)
  rw [mul_comm]
  convert h using 3
  ring

/-- Pointwise bound on the Navier symbol of an essentially bounded integrable profile. -/
theorem enorm_bil_le_of_bound (u : ES → ComplexSpace) {R B : ℝ} (hR : 0 ≤ R)
    (hu : ∀ᵐ ζ ∂(volume : Measure ES), ‖u ζ‖ ≤ R)
    (hL : ∫⁻ η, ‖u η‖ₑ ≤ 3 * ENNReal.ofReal B) (ξ : ES) :
    ‖continuousNavierBilinear u u ξ‖ₑ ≤ ENNReal.ofReal (‖ξ‖ * (27 * R * B)) := by
  refine (enorm_bilinear_le u u ξ).trans ?_
  have hc : convE u u ξ ≤ (3 * ENNReal.ofReal B) * ENNReal.ofReal R := by
    unfold convE
    calc ∫⁻ η, ‖u η‖ₑ * ‖u (ξ - η)‖ₑ ≤ ∫⁻ η, ‖u η‖ₑ * ENNReal.ofReal R := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_sub_left hu ξ] with η h
          refine mul_le_mul' le_rfl ?_
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h
      _ = (∫⁻ η, ‖u η‖ₑ) * ENNReal.ofReal R := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (3 * ENNReal.ofReal B) * ENNReal.ofReal R := mul_le_mul' hL le_rfl
  calc 9 * ‖ξ‖ₑ * convE u u ξ ≤ 9 * ‖ξ‖ₑ * ((3 * ENNReal.ofReal B) * ENNReal.ofReal R) :=
        mul_le_mul' le_rfl hc
    _ = ENNReal.ofReal (‖ξ‖ * (27 * R * B)) := by
      rw [← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hR), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
      ring

/-- **The Duhamel term of an essentially bounded path is essentially bounded.** -/
theorem duhamel_mem_Zb (hν : 0 < ν) (hT : 0 < T) (y : C(Icc (0 : ℝ) T, V1)) {R B : ℝ}
    (hR : 0 ≤ R) (hy : y ∈ linfSet T R) (hyB : ‖y‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (i : Fin 3) :
    duhamel ν hT.le y y t i ∈ Zb (27 * R * B * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t)) := by
  obtain ⟨v, hvm, hv⟩ := exists_joint_rep hT.le y
  -- the per-time properties of the representative
  set P : ℝ → Prop := fun s => ∀ i : Fin 3, (fun ξ => v s ξ i) =ᵐ[volume] ⇑(extend hT.le y s i)
  have hgood : ∀ s ∈ Icc (0 : ℝ) T, P s →
      (∀ᵐ ζ ∂(volume : Measure ES), ‖v s ζ‖ ≤ R) ∧ ∫⁻ η, ‖v s η‖ₑ ≤ 3 * ENNReal.ofReal B := by
    intro s hs hPs
    have hext : extend hT.le y s = y ⟨s, hs⟩ := by
      unfold WienerLocalMild.extend; rw [projIcc_of_mem hT.le hs]
    refine ⟨?_, ?_⟩
    · have hc : ∀ᵐ ζ ∂(volume : Measure ES), ∀ j : Fin 3, ‖v s ζ j‖ ≤ R := by
        refine ae_all_iff.mpr fun j => ?_
        filter_upwards [hPs j, hy ⟨s, hs⟩ j] with ζ h1 h2
        rw [h1, hext]; exact h2
      filter_upwards [hc] with ζ h
      exact (pi_norm_le_iff_of_nonneg hR).mpr h
    · calc ∫⁻ η, ‖v s η‖ₑ ≤ ∫⁻ η, ∑ j : Fin 3, ‖v s η j‖ₑ :=
            lintegral_mono fun η => WienerMildGood.enorm_le_sum_coord _
        _ = ∑ j : Fin 3, ∫⁻ η, ‖v s η j‖ₑ := by
            refine lintegral_finsetSum _ fun j _ => ?_
            exact (show Measurable (fun η => v s η j) from
              ((hvm j).comp_measurable (measurable_id.prodMk measurable_const)).measurable).enorm
        _ ≤ ∑ _j : Fin 3, ENNReal.ofReal B := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [lintegral_congr_ae (by filter_upwards [hPs j] with η h; rw [h]),
              ← L1.ofReal_norm_eq_lintegral]
            exact ENNReal.ofReal_le_ofReal ((norm_le_pi_norm _ j).trans
              ((norm_extend_le hT.le y s).trans hyB))
        _ = 3 * ENNReal.ofReal B := by simp
  -- transfer the a.e. time property along `σ ↦ t - σ`
  have hvσ : ∀ᵐ σ ∂(volume.restrict (Ioc (0 : ℝ) T)), t - σ ∈ Icc (0 : ℝ) T → P (t - σ) := by
    have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) T → P s :=
      (ae_restrict_iff' measurableSet_Icc).mp hv
    exact ae_restrict_of_ae
      ((Measure.measurePreserving_sub_left (volume : Measure ℝ) t).quasiMeasurePreserving.ae h1)
  set c : ℝ := 27 * R * B with hc
  have hB : 0 ≤ B := (norm_nonneg y).trans hyB
  have hc0 : 0 ≤ c := by positivity
  set g : ℝ → ℝ := (Ioc 0 t).indicator (fun σ => singWeight ν σ * c) with hg
  have hgint : Integrable g (volume.restrict (Ioc (0 : ℝ) T)) := by
    rw [hg, integrable_indicator_iff measurableSet_Ioc]
    refine ((integrableOn_singWeight ν ht.1).mul_const c).mono_measure ?_
    exact Measure.restrict_mono subset_rfl Measure.restrict_le_self
  have hgval : ∫ σ in Ioc (0 : ℝ) T, g σ = c * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
    rw [hg, setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_self,
      min_eq_right ht.2, integral_mul_const, integral_singWeight ν ht.1]
    ring
  show ∀ᵐ ξ ∂(volume : Measure ES), ‖(duhamel ν hT.le y y t i) ξ‖ ≤ _
  filter_upwards [duhamel_coord_ae_eq hν hT.le y v hvm hv ht i] with ξ hξ
  rw [hξ, ← integral_gDuh_eq ν v ht.1 ht.2 i ξ, ← hgval]
  refine norm_integral_le_of_norm_le hgint ?_
  filter_upwards [hvσ, ae_restrict_mem measurableSet_Ioc] with σ hP hσ
  by_cases hle : σ ≤ t
  · have hs : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hσ.1, ht.2]⟩
    obtain ⟨hb1, hb2⟩ := hgood (t - σ) hs (hP hs)
    have hbil := enorm_bil_le_of_bound (v (t - σ)) hR hb1 hb2 ξ
    have hbil' : ‖continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ‖ ≤ ‖ξ‖ * c := by
      rw [← ofReal_norm] at hbil
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbil
    unfold gDuh
    rw [Set.indicator_of_mem (show σ ∈ Iic t from hle), hg,
      Set.indicator_of_mem (show σ ∈ Ioc 0 t from ⟨hσ.1, hle⟩), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
    calc heatFactor ν σ ξ * ‖continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ i‖
        ≤ heatFactor ν σ ξ * (‖ξ‖ * c) :=
          mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ i).trans hbil')
            (heatFactor_nonneg _ _ _)
      _ = (heatFactor ν σ ξ * ‖ξ‖) * c := by ring
      _ ≤ singWeight ν σ * c := mul_le_mul_of_nonneg_right (heat_mul_norm_le hν hσ.1 ξ) hc0
  · unfold gDuh
    rw [Set.indicator_of_notMem (show σ ∉ Iic t from hle), norm_zero, hg,
      Set.indicator_of_notMem (show σ ∉ Ioc 0 t from fun h => hle h.2)]

/-! ## The fixed point stays essentially bounded -/

theorem add_mem_Zb {f g : L1C} {a b : ℝ} (hf : f ∈ Zb a) (hg : g ∈ Zb b) : f + g ∈ Zb (a + b) := by
  show ∀ᵐ ξ ∂(volume : Measure ES), ‖(f + g) ξ‖ ≤ a + b
  filter_upwards [Lp.coeFn_add f g, hf, hg] with ξ h h1 h2
  rw [h, Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem Zb_mono {f : L1C} {a b : ℝ} (hf : f ∈ Zb a) (hab : a ≤ b) : f ∈ Zb b := by
  show ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ ≤ b
  filter_upwards [hf] with ξ h using h.trans hab

theorem heatOp_zero (hν : 0 ≤ ν) (a₀ : V1) : heatOp ν 0 a₀ = a₀ := by
  funext i
  rw [heatOp_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL (heatLinf ν 0) (a₀ i), coeFn_heatLinf hν 0] with ξ h1 h2
  rw [h1, h2]
  simp [heatFactor]

/-- **Essential boundedness of the fixed point** on the horizon `10⁶ T ‖a₀‖² ≤ ν`. -/
theorem fixedPoint_mem_linfSet (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 6 * T * ‖a₀‖ ^ 2 ≤ ν) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ i, a₀ i ∈ Zb A)
    (x : C(Icc (0 : ℝ) T, V1)) (hxle : ‖x‖ ≤ 2 * ‖a₀‖)
    (hxeq : x = heatPath hν a₀ + duhamelPath hν hT.le x x) : x ∈ linfSet T (2 * A) := by
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T with hC
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hC0 : 0 < C := by rw [hC]; positivity
  set y : C(Icc (0 : ℝ) T, V1) := heatPath hν a₀ with hy
  have hyle : ‖y‖ ≤ ‖a₀‖ := norm_heatPath_le hν a₀
  have hy0 : ‖a₀‖ ≤ ‖y‖ := by
    have h := y.norm_coe_le_norm ⟨0, le_rfl, hT.le⟩
    have h0 : y ⟨0, le_rfl, hT.le⟩ = a₀ := heatOp_zero hν.le a₀
    rwa [h0] at h
  have hroot : 1000 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [show (10 : ℝ) ^ 6 * T * ‖a₀‖ ^ 2 = (1000 * (Real.sqrt T * ‖a₀‖)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]; ring,
      Real.sqrt_sq (by positivity)] at h
  have hsmallC : 4 * C * ‖y‖ < 1 := by
    have h1 : 4 * C * ‖y‖ ≤ 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν := by
      rw [hC, div_eq_mul_inv]
      have : 4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖y‖ ≤
          4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖a₀‖ :=
        mul_le_mul_of_nonneg_left hyle (by positivity)
      nlinarith [this]
    have h2 : 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν < 1 := by
      rw [div_lt_one hsν]
      have : 0 ≤ Real.sqrt T * ‖a₀‖ := by positivity
      nlinarith
    linarith
  have hB := norm_duhamelPath_le hν hT.le
  have hdiff := duhamelPath_diff hν hT.le
  have hyS : y ∈ linfSet T (2 * A) := fun t i =>
    Zb_mono (heatOp_mem_Zb hν.le t a₀ i (ha i)) (by linarith)
  have hmap : ∀ z ∈ linfSet T (2 * A), ‖z‖ ≤ 2 * ‖y‖ →
      y + duhamelPath hν hT.le z z ∈ linfSet T (2 * A) := by
    intro z hz hzn t i
    have hzB : ‖z‖ ≤ 2 * ‖a₀‖ := hzn.trans (by linarith)
    have hD := duhamel_mem_Zb hν hT z (by linarith) hz hzB t.2 i
    have hsum := add_mem_Zb (heatOp_mem_Zb hν.le (t : ℝ) a₀ i (ha i)) hD
    refine Zb_mono hsum ?_
    have hst : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt t.2.2
    have hkey : 27 * (2 * A) * (2 * ‖a₀‖) * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) ≤ A := by
      have h1 : (Real.sqrt ν)⁻¹ * (Real.sqrt t * ‖a₀‖) ≤ 1 / 1000 := by
        rw [inv_mul_le_iff₀ hsν]
        have : Real.sqrt t * ‖a₀‖ ≤ Real.sqrt T * ‖a₀‖ :=
          mul_le_mul_of_nonneg_right hst (norm_nonneg _)
        linarith
      have h2 : 27 * (2 * A) * (2 * ‖a₀‖) * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) =
          216 * A * ((Real.sqrt ν)⁻¹ * (Real.sqrt t * ‖a₀‖)) := by ring
      rw [h2]
      nlinarith
    linarith
  obtain ⟨xn, hxnS, hxnle, hxneq⟩ := picard_small_data_on hC0 hB hdiff y hsmallC
    (linfSet T (2 * A)) (isClosed_linfSet _) hyS hmap
  have hxx : xn = x := picard_unique hC0 hB hdiff y hsmallC hxnle
    (hxle.trans (by linarith)) hxneq hxeq
  rw [← hxx]
  exact hxnS

end Navier.Analysis.WienerLinfBound

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLinfBound.fixedPoint_mem_linfSet
