import Navier.Analysis.WienerPhysicalAssembly

/-!
# Joint smoothness of the Wiener pressure

The Fourier pressure coefficient `Q̂ = ∑ⱼₖ (ξⱼξₖ/‖ξ‖²)(wⱼ ⋆ wₖ)` is a second
bounded bilinear symbol of the convolution array, with multiplier bounded by one.
Along the derivative hierarchy `W` of `WienerPointwiseODE` its Leibniz tower

`P k = ∑_{m ≤ k} C(k,m) pBil (W m) (W (k-m))`

is a derivative tower of majorized continuous families, hence (by
`towerPath`/`contDiffOn_phys`) `(t,x) ↦ 𝓕⁻ Q̂(t)(x)` is jointly `C^∞` on
`[0,T) × ℝ³`, and the rescaled pressure satisfies `SmoothPressureBefore`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

namespace Navier.Analysis.WienerPressureSmooth

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerPhysicalPDE
open Navier.Analysis.WienerPhysicalAssembly

/-! ## The pressure symbol -/

/-- The multiplier `ξⱼξₖ/‖ξ‖²` (zero at the origin). -/
def qc (ξ : ES) (j k : Fin 3) : ℂ :=
  ((ξ j : ℝ) : ℂ) * ((ξ k : ℝ) : ℂ) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem norm_qc_le (ξ : ES) (j k : Fin 3) : ‖qc ξ j k‖ ≤ 1 := by
  unfold qc
  by_cases hξ : ξ = 0
  · subst hξ; simp
  have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_le_one hpos,
    norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    ← abs_mul]
  exact norm_coord_mul_le ξ j k

theorem measurable_qc (j k : Fin 3) : Measurable (fun ξ : ES => qc ξ j k) := by
  unfold qc
  exact ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).measurable.mul
    (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ k)).measurable).div
    (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).measurable

/-- The unit vector carrying the scalar pressure symbol in the vector framework. -/
def e0 : ComplexSpace := Pi.single 0 1

theorem enorm_e0_le : ‖e0‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ENNReal.ofReal_le_one]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun l => ?_
  by_cases hl : l = 0
  · subst hl; simp [e0]
  · simp [e0, Pi.single_apply, hl]

/-- The pressure symbol of a convolution array. -/
def qOfConv (ξ : ES) (c : Fin 3 → Fin 3 → ℂ) : ComplexSpace :=
  (∑ j : Fin 3, ∑ k : Fin 3, qc ξ j k * c j k) • e0

/-- `qOfConv ξ` as a continuous linear map. -/
def qCLM (ξ : ES) : (Fin 3 → Fin 3 → ℂ) →L[ℂ] ComplexSpace :=
  (∑ j : Fin 3, ∑ k : Fin 3, qc ξ j k • ((ContinuousLinearMap.proj k).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) j))).smulRight e0

theorem qCLM_apply (ξ : ES) (c : Fin 3 → Fin 3 → ℂ) : qCLM ξ c = qOfConv ξ c := by
  simp [qCLM, qOfConv, ContinuousLinearMap.sum_apply, smul_eq_mul]

/-- The bilinear pressure symbol. -/
def pBil (u v : ES → ComplexSpace) (ξ : ES) : ComplexSpace :=
  qOfConv ξ (fun j k => ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
    (fun η => v η k)) ξ)

theorem stronglyMeasurable_pBil {u v : ES → ComplexSpace} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) : StronglyMeasurable (pBil u v) := by
  have h : Measurable (fun ξ => ∑ j : Fin 3, ∑ k : Fin 3, qc ξ j k *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η k)) ξ) :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
      (measurable_qc j k).mul (stronglyMeasurable_conv_coord hu hv j k).measurable
  exact (h.smul_const e0).stronglyMeasurable

theorem enorm_pBil_le (u v : ES → ComplexSpace) (ξ : ES) :
    ‖pBil u v ξ‖ₑ ≤ 9 * convE u v ξ := by
  unfold pBil qOfConv
  rw [enorm_smul]
  refine (mul_le_of_le_one_right' enorm_e0_le).trans ?_
  refine (enorm_sum_le _ _).trans ?_
  have hk : ∀ j : Fin 3, ‖∑ k : Fin 3, qc ξ j k *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η k)) ξ‖ₑ ≤
      3 * convE u v ξ := by
    intro j
    refine (enorm_sum_le _ _).trans ?_
    calc ∑ k : Fin 3, ‖qc ξ j k *
          ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η k)) ξ‖ₑ
        ≤ ∑ _k : Fin 3, convE u v ξ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [enorm_mul]
          have hq : ‖qc ξ j k‖ₑ ≤ 1 := by
            rw [← ofReal_norm, ENNReal.ofReal_le_one]; exact norm_qc_le ξ j k
          exact (mul_le_of_le_one_left' hq).trans (enorm_conv_coord_le u v j k ξ)
      _ = 3 * convE u v ξ := by simp
  calc ∑ j : Fin 3, ‖∑ k : Fin 3, qc ξ j k *
        ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η k)) ξ‖ₑ
      ≤ ∑ _j : Fin 3, 3 * convE u v ξ := Finset.sum_le_sum fun j _ => hk j
    _ = 9 * convE u v ξ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc]; norm_num

/-- **Majorized continuous families are closed under the pressure symbol.** -/
theorem good_pBil {T : ℝ} {U V : ℝ → ES → ComplexSpace} (hU : Good T U) (hV : Good T V) :
    Good T (fun t => pBil (U t) (V t)) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, hUc⟩ := hU
  obtain ⟨hVm, MV, hMV, hVb, hVmom, hVc⟩ := hV
  refine ⟨fun t => stronglyMeasurable_pBil (hUm t) (hVm t),
    fun ξ => 9 * ∫⁻ η, MU η * MV (ξ - η), ?_, ?_, ?_, ?_⟩
  · exact measurable_const.mul (measurable_convMaj hMU hMV)
  · refine Eventually.of_forall fun ξ t ht => (enorm_pBil_le _ _ ξ).trans ?_
    refine mul_le_mul' le_rfl ?_
    unfold convE
    refine lintegral_mono_ae ?_
    filter_upwards [hUb, ae_sub_left hVb ξ] with η h1 h2
    exact mul_le_mul' (h1 t ht) (h2 t ht)
  · intro n
    have h := lintegral_weight_convE_le n MU MV hMU hMV
    have hmm : Measurable fun ξ : ES =>
        ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, MU η * MV (ξ - η) :=
      (ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).mul
        (measurable_convMaj hMU hMV)
    have heq : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * (9 * ∫⁻ η, MU η * MV (ξ - η)) =
        9 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ∫⁻ η, MU η * MV (ξ - η) := by
      rw [← lintegral_const_mul _ hmm]
      refine lintegral_congr fun ξ => ?_
      ring
    rw [heq]
    refine ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top ?_ h)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (hUmom _) (lintegral_ne_top_of_mom hVmom)),
      ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (lintegral_ne_top_of_mom hUmom)
        (hVmom _))⟩
  · filter_upwards [ae_convMaj_ne_top hMU hMV (lintegral_ne_top_of_mom hUmom)
      (lintegral_ne_top_of_mom hVmom)] with ξ hξ
    have hc : ∀ j i : Fin 3, ContinuousOn (fun t => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ,
        volume] (fun η => V t η i)) ξ) (Icc (0 : ℝ) T) := fun j i =>
      continuousOn_conv_coord hUm hVm hUb hVb hUc hVc
        ((hMU.comp measurable_id).mul (hMV.comp (measurable_const.sub measurable_id))) hξ j i
    have harr : ContinuousOn (fun t => fun j k => ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ,
        volume] (fun η => V t η k)) ξ) (Icc (0 : ℝ) T) :=
      continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => hc j k
    have h := (qCLM ξ).continuous.comp_continuousOn harr
    refine h.congr fun t _ => ?_
    simp only [Function.comp_apply, qCLM_apply]
    rfl

/-- **Product rule for the pressure symbol along the hierarchy.** -/
theorem hasTimeDeriv_pBil {T : ℝ} {U U' V V' : ℝ → ES → ComplexSpace}
    (hU : Good T U) (hU' : Good T U') (hV : Good T V) (hV' : Good T V')
    (hUd : HasTimeDeriv T U U') (hVd : HasTimeDeriv T V V') :
    HasTimeDeriv T (fun t => pBil (U t) (V t))
      (fun t ξ => pBil (U' t) (V t) ξ + pBil (U t) (V' t) ξ) := by
  obtain ⟨hUm, MU, hMU, hUb, hUmom, -⟩ := hU
  obtain ⟨hU'm, MU', hMU', hU'b, hU'mom, -⟩ := hU'
  obtain ⟨hVm, MV, hMV, hVb, hVmom, -⟩ := hV
  obtain ⟨hV'm, MV', hMV', hV'b, hV'mom, -⟩ := hV'
  filter_upwards [ae_convMaj_ne_top hMU hMV (lintegral_ne_top_of_mom hUmom)
      (lintegral_ne_top_of_mom hVmom),
    ae_convMaj_ne_top hMU' hMV (lintegral_ne_top_of_mom hU'mom) (lintegral_ne_top_of_mom hVmom),
    ae_convMaj_ne_top hMU hMV' (lintegral_ne_top_of_mom hUmom) (lintegral_ne_top_of_mom hV'mom)]
    with ξ h1 h2 h3 t₀ ht₀
  set c : ℝ → Fin 3 → Fin 3 → ℂ := fun t j i =>
    ((fun η => U t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V t η i)) ξ with hc
  set c₁ : Fin 3 → Fin 3 → ℂ := fun j i =>
    ((fun η => U' t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V t₀ η i)) ξ
  set c₂ : Fin 3 → Fin 3 → ℂ := fun j i =>
    ((fun η => U t₀ η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => V' t₀ η i)) ξ
  have hcd : HasDerivAt c (c₁ + c₂) t₀ := by
    refine hasDerivAt_pi.mpr fun j => hasDerivAt_pi.mpr fun i => ?_
    exact hasDerivAt_conv_coord hUm hU'm hVm hV'm hMU hMU' hMV hMV' hUb hU'b hVb hV'b hUd hVd
      h1 h2 h3 j i ht₀
  have hL := ((qCLM ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hcd
  have hfun : (fun s => pBil (U s) (V s) ξ) = ((qCLM ξ).restrictScalars ℝ) ∘ c := by
    funext s
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', qCLM_apply]
    rfl
  rw [hfun]
  refine hL.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', map_add, qCLM_apply]
  rfl

/-! ## The pressure tower -/

/-- `P k = ∑_{m ≤ k} C(k,m) pBil (W m) (W (k-m))`. -/
def Pk (ν : ℝ) (w : ℝ → ES → ComplexSpace) (k : ℕ) : ℝ → ES → ComplexSpace :=
  fun t ξ => ∑ m ∈ Finset.range (k + 1), k.choose m • pBil (W ν w m t) (W ν w (k - m) t) ξ

theorem good_Pk {T ν : ℝ} (hν : 0 ≤ ν) {w : ℝ → ES → ComplexSpace} (hw : Good T w) (k : ℕ) :
    Good T (Pk ν w k) :=
  good_sum _ fun m _ => good_nsmul (good_pBil (good_W hν hw m) (good_W hν hw (k - m))) _

theorem hasTimeDeriv_Pk {T ν : ℝ} (hν : 0 ≤ ν) {w : ℝ → ES → ComplexSpace} (hw : Good T w)
    (h0 : HasTimeDeriv T (W ν w 0) (W ν w 1)) (k : ℕ) :
    HasTimeDeriv T (Pk ν w k) (Pk ν w (k + 1)) := by
  have hG := good_W hν hw
  have hdW := hasTimeDeriv_W hν hw h0
  have hd := hasTimeDeriv_sum (Finset.range (k + 1)) (U := fun m t ξ =>
      k.choose m • pBil (W ν w m t) (W ν w (k - m) t) ξ)
    (U' := fun m t ξ => k.choose m • (pBil (W ν w (m + 1) t) (W ν w (k - m) t) ξ +
      pBil (W ν w m t) (W ν w (k - m + 1) t) ξ))
    fun m _ => hasTimeDeriv_nsmul (hasTimeDeriv_pBil (hG m) (hG (m + 1)) (hG (k - m))
      (hG (k - m + 1)) (hdW m) (hdW (k - m))) _
  filter_upwards [hd] with ξ hξ t ht
  refine (hξ t ht).congr_deriv ?_
  show _ = ∑ m ∈ Finset.range (k + 1 + 1),
    (k + 1).choose m • pBil (W ν w m t) (W ν w (k + 1 - m) t) ξ
  rw [Finset.sum_choose_succ_nsmul
    (fun a b => pBil (W ν w a t) (W ν w b t) ξ) k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk := Finset.mem_range.mp hm
  rw [smul_add, show k - m + 1 = k + 1 - m by omega]
  exact add_comm _ _

theorem Qhat_eq_Pk_zero (ν : ℝ) (w : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) :
    Qhat w t ξ = Pk ν w 0 t ξ 0 := by
  show Qhat w t ξ = (∑ m ∈ Finset.range (0 + 1),
    (0 : ℕ).choose m • pBil (W ν w m t) (W ν w (0 - m) t) ξ) 0
  rw [Finset.sum_range_one, Nat.choose_zero_right, one_smul, Nat.sub_zero, W_zero]
  show _ = ((∑ j : Fin 3, ∑ k : Fin 3, qc ξ j k *
    ((fun η => w t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => w t η k)) ξ) • e0) 0
  rw [Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, mul_one]
  unfold Qhat qc cc
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Joint smoothness of the Fourier pressure** on `[0,T) × ℝ³`. -/
theorem contDiffOn_pressure {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
    {w : ℝ → ES → ComplexSpace}
    (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
    (hG : Good T w) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ES => 𝓕⁻ (Qhat w z.1) z.2)
      (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := by
  have hGP := good_Pk hν.le hG
  have hdP := hasTimeDeriv_Pk hν.le hG (hasTimeDeriv_W_zero hν a hfix hG)
  set P := towerPath hT (Pk ν w) hGP 0 hdP
  refine (contDiffOn_phys hT P).congr fun z hz => ?_
  show 𝓕⁻ (Qhat w z.1) z.2 = 𝓕⁻ (⇑(towerD hT (Pk ν w) hGP 0 0 0 z.1)) z.2
  rw [fourierInv_congr (coeFn_towerD hT (Pk ν w) hGP 0 0 0 z.1) z.2]
  unfold towerSym
  rw [projIcc_of_mem hT.le (Ico_subset_Icc_self hz.1)]
  have hfun : Qhat w z.1 = fun ξ => mono 0 ξ * Pk ν w 0 z.1 ξ 0 := by
    funext ξ
    rw [Qhat_eq_Pk_zero ν, mono_zero, one_mul]
  rw [hfun]

/-- **`SmoothPressureBefore`** for the rescaled pressure. -/
theorem smoothPressureBefore_physP {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (a : ES → ComplexSpace) {w : ℝ → ES → ComplexSpace}
    (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
    (hG : Good T w) : SmoothPressureBefore T (physP w) := by
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1, euclidPoint z.2)) :=
    contDiff_fst.prodMk (eCLM.contDiff.comp contDiff_snd)
  have hms : MapsTo (fun z : ℝ × Space => (z.1, euclidPoint z.2)) (spacetimeBefore T)
      (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := fun z hz => ⟨hz.1, mem_univ _⟩
  have h := (contDiffOn_pressure hT hν a hfix hG).comp hmap.contDiffOn hms
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn h)

end Navier.Analysis.WienerPressureSmooth

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPressureSmooth.smoothPressureBefore_physP
