import Navier.Analysis.WienerSchwartzSmooth

/-!
# Reality of the Wiener solution: conjugate reflection

`R f (ξ) = conj f (-ξ)` on `L¹(ℝ³; ℂ)`.  This module proves that `R` is an
isometry commuting with convolution, with the heat and Duhamel multipliers and
hence with the Picard map, so that the unique fixed point of a Hermitian datum
is `R`-invariant; its inverse Fourier transform is then real.

First part: the pointwise conjugate reflection and its interaction with the
inverse Fourier transform.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution ComplexConjugate

namespace Navier.Analysis.WienerReality

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerLocalMild

/-- Pointwise conjugate reflection. -/
def reflC (f : ES → ℂ) : ES → ℂ := fun ξ => conj (f (-ξ))

theorem integrable_reflC {f : ES → ℂ} (hf : Integrable f) : Integrable (reflC f) := by
  have h := hf.comp_neg
  refine h.norm.mono' ?_ (Eventually.of_forall fun ξ => by simp [reflC])
  exact Complex.continuous_conj.comp_aestronglyMeasurable h.1

theorem phaseCLM_neg (v x : ES) : phaseCLM (-v) x = conj (phaseCLM v x) := by
  rw [phaseCLM_apply, phaseCLM_apply, inner_neg_left]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- `conj (𝓕⁻ g y) = 𝓕⁻ (reflC g) y`. -/
theorem conj_fourierInv (g : ES → ℂ) (y : ES) : conj (𝓕⁻ g y) = 𝓕⁻ (reflC g) y := by
  rw [fourierInv_eq_exp, fourierInv_eq_exp, ← integral_conj]
  have h := integral_neg_eq_self (fun v : ES => Complex.exp (phaseCLM (-v) y) * reflC g (-v))
    (volume : Measure ES)
  simp only [neg_neg] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [reflC, neg_neg, map_mul, phaseCLM_neg, ← Complex.exp_conj]

/-! ## Conjugate reflection on `L¹` -/

theorem ae_neg {P : ES → Prop} (h : ∀ᵐ ξ ∂(volume : Measure ES), P ξ) :
    ∀ᵐ ξ ∂(volume : Measure ES), P (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure ES)).quasiMeasurePreserving.ae h

/-- Conjugate reflection of an `L¹` class. -/
def Rc (f : L1C) : L1C := (integrable_reflC (L1.integrable_coeFn f)).toL1 _

theorem coeFn_Rc (f : L1C) : ⇑(Rc f) =ᵐ[volume] reflC ⇑f := Integrable.coeFn_toL1 _

theorem reflC_congr {f g : ES → ℂ} (h : f =ᵐ[volume] g) : reflC f =ᵐ[volume] reflC g := by
  filter_upwards [ae_neg h] with ξ hξ
  simp [reflC, hξ]

theorem Rc_add (f g : L1C) : Rc (f + g) = Rc f + Rc g := by
  apply Lp.ext
  filter_upwards [coeFn_Rc (f + g), Lp.coeFn_add (Rc f) (Rc g), coeFn_Rc f, coeFn_Rc g,
    reflC_congr (Lp.coeFn_add f g)] with ξ h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5]
  simp [reflC]

theorem Rc_smul (c : ℝ) (f : L1C) : Rc (c • f) = c • Rc f := by
  apply Lp.ext
  filter_upwards [coeFn_Rc (c • f), Lp.coeFn_smul c (Rc f), coeFn_Rc f,
    reflC_congr (Lp.coeFn_smul c f)] with ξ h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4]
  simp [reflC, Complex.real_smul]

theorem norm_Rc (f : L1C) : ‖Rc f‖ = ‖f‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
    integral_congr_ae (by filter_upwards [coeFn_Rc f] with ξ h; rw [h])]
  have h := integral_neg_eq_self (fun ξ : ES => ‖f ξ‖) (volume : Measure ES)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp [reflC]

/-- Conjugate reflection as a real-linear isometry-bounded operator. -/
def RcL : L1C →L[ℝ] L1C :=
  LinearMap.mkContinuous { toFun := Rc, map_add' := Rc_add, map_smul' := Rc_smul } 1
    (fun f => by simp [norm_Rc])

theorem RcL_apply (f : L1C) : RcL f = Rc f := rfl

theorem reflC_convolution (f g : ES → ℂ) (ξ : ES) :
    reflC (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ =
      (reflC f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] reflC g) ξ := by
  simp only [reflC, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_conj]
  have h := integral_neg_eq_self (fun η : ES => conj (f (-η)) * conj (g (-(ξ - η))))
    (volume : Measure ES)
  simp only [neg_neg] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [map_mul]
  congr 2
  abel_nf

theorem Rc_conv (f g : L1C) : Rc (conv f g) = conv (Rc f) (Rc g) := by
  apply Lp.ext
  have hc : (⇑(Rc f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑(Rc g)) =
      reflC ⇑f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] reflC ⇑g :=
    convolution_congr _ (coeFn_Rc f) (coeFn_Rc g)
  filter_upwards [coeFn_Rc (conv f g), coeFn_convFun (Rc f) (Rc g),
    reflC_congr (coeFn_convFun f g)] with ξ h1 h2 h3
  rw [h1, conv_apply, conv_apply, h2, h3, hc, reflC_convolution]

/-- A multiplier with a conjugate-even symbol commutes with `Rc`. -/
theorem Rc_mulL (m : LinfC) {s : ES → ℂ} (hms : ⇑m =ᵐ[volume] s)
    (hs : ∀ ξ, conj (s (-ξ)) = s ξ) (f : L1C) : Rc (mulL m f) = mulL m (Rc f) := by
  apply Lp.ext
  filter_upwards [coeFn_Rc (mulL m f), coeFn_mulL m (Rc f), coeFn_Rc f, hms,
    reflC_congr (coeFn_mulL m f), ae_neg hms] with ξ h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5]
  simp only [reflC, map_mul]
  rw [h6, hs]

/-! ## The heat and kernel symbols are conjugate-even -/

theorem heatFactor_neg (ν τ : ℝ) (ξ : ES) : heatFactor ν τ (-ξ) = heatFactor ν τ ξ := by
  simp [heatFactor, norm_neg]

theorem heat_symbol_even (ν t : ℝ) (ξ : ES) :
    conj ((heatFactor ν (max t 0) (-ξ) : ℝ) : ℂ) = (heatFactor ν (max t 0) ξ : ℂ) := by
  rw [Complex.conj_ofReal, heatFactor_neg]

theorem lerayDerivSymbol_even (i j k : Fin 3) (ξ : ES) :
    conj (lerayDerivSymbol i j k (-ξ)) = lerayDerivSymbol i j k ξ := by
  rw [lerayDerivSymbol_formula, lerayDerivSymbol_formula]
  have hq : Navier.Analysis.FourierMajorant.spaceProj (-ξ) =
      -Navier.Analysis.FourierMajorant.spaceProj ξ := map_neg _ ξ
  rw [hq]
  fin_cases i <;> fin_cases k <;>
    simp [Fin.sum_univ_three, Pi.single_apply, Complex.conj_ofReal, dotProduct, map_neg,
      map_div₀, map_sub, map_mul, map_add] <;> ring

theorem kernelSymbol_even (ν τ : ℝ) (i j k : Fin 3) (ξ : ES) :
    conj (kernelSymbol ν τ i j k (-ξ)) = kernelSymbol ν τ i j k ξ := by
  unfold kernelSymbol
  rw [map_mul, Complex.conj_ofReal, heatFactor_neg, lerayDerivSymbol_even]

/-! ## Commutation with the Picard map -/

theorem Rc_Rc (f : L1C) : Rc (Rc f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_Rc (Rc f), reflC_congr (coeFn_Rc f)] with ξ h1 h2
  rw [h1, h2]
  simp [reflC]

theorem Rc_zero : Rc 0 = 0 := by
  have h := RcL.map_zero
  exact h

theorem Rc_sum {ι : Type*} (s : Finset ι) (f : ι → L1C) : Rc (∑ i ∈ s, f i) = ∑ i ∈ s, Rc (f i) :=
  map_sum RcL f s

theorem Rc_mulL_kernel (ν σ : ℝ) (i j k : Fin 3) (f : L1C) :
    Rc (mulL (kernelLinf ν σ i j k) f) = mulL (kernelLinf ν σ i j k) (Rc f) := by
  by_cases h : 0 < ν ∧ 0 < σ
  · exact Rc_mulL _ (coeFn_kernelLinf h.1 h.2 i j k) (kernelSymbol_even ν σ i j k) f
  · have h0 : kernelLinf ν σ i j k = 0 := by unfold kernelLinf; rw [dif_neg h]
    rw [h0, map_zero, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, Rc_zero]

theorem Rc_mulL_heat (ν t : ℝ) (f : L1C) :
    Rc (mulL (heatLinf ν t) f) = mulL (heatLinf ν t) (Rc f) := by
  by_cases h : 0 ≤ ν
  · exact Rc_mulL _ (coeFn_heatLinf h t) (heat_symbol_even ν t) f
  · have h0 : heatLinf ν t = 0 := by unfold heatLinf; rw [dif_neg h]
    rw [h0, map_zero, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, Rc_zero]

/-- Coordinatewise reflection of a velocity coefficient vector. -/
def RV (v : V1) : V1 := fun i => Rc (v i)

/-- Reflection of a tensor. -/
def RW (W : W1) : W1 := fun j k => Rc (W j k)

theorem RV_kernelOp (ν σ : ℝ) (W : W1) : RV (kernelOp ν σ W) = kernelOp ν σ (RW W) := by
  funext i
  simp only [RV, RW, kernelOp, tensorMulOp_apply, Rc_sum, Rc_mulL_kernel]

theorem RW_tensorConv (u v : V1) : RW (tensorConv u v) = tensorConv (RV u) (RV v) := by
  funext j k
  simp only [RW, RV, tensorConv_apply]
  exact Rc_conv (u j) (v k)

theorem RV_heatOp (ν t : ℝ) (v : V1) : RV (heatOp ν t v) = heatOp ν t (RV v) := by
  funext i
  simp only [RV, heatOp_apply, Rc_mulL_heat]

theorem RV_RV (v : V1) : RV (RV v) = v := by funext i; exact Rc_Rc (v i)

theorem norm_RV (v : V1) : ‖RV v‖ = ‖v‖ := by
  have h1 : ∀ u : V1, ‖RV u‖ ≤ ‖u‖ := fun u =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
      rw [show RV u i = Rc (u i) from rfl, norm_Rc]; exact norm_le_pi_norm u i
  refine le_antisymm (h1 v) ?_
  have := h1 (RV v)
  rwa [RV_RV] at this

/-- `RV` as a real-linear continuous operator. -/
def RVL : V1 →L[ℝ] V1 :=
  ContinuousLinearMap.pi fun i => RcL.comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => L1C) i)

theorem RVL_apply (v : V1) : RVL v = RV v := rfl

theorem RV_add (u v : V1) : RV (u + v) = RV u + RV v := by
  simp only [← RVL_apply, map_add]

/-- Reflection of a Wiener path. -/
def Rpath {T : ℝ} (x : C(Icc (0 : ℝ) T, V1)) : C(Icc (0 : ℝ) T, V1) :=
  ⟨fun t => RV (x t), RVL.continuous.comp x.continuous⟩

theorem Rpath_apply {T : ℝ} (x : C(Icc (0 : ℝ) T, V1)) (t : Icc (0 : ℝ) T) :
    Rpath x t = RV (x t) := rfl

theorem norm_Rpath {T : ℝ} (x : C(Icc (0 : ℝ) T, V1)) : ‖Rpath x‖ = ‖x‖ := by
  have h1 : ∀ y : C(Icc (0 : ℝ) T, V1), ‖Rpath y‖ ≤ ‖y‖ := fun y =>
    (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun t => by
      rw [Rpath_apply, norm_RV]; exact y.norm_coe_le_norm t
  refine le_antisymm (h1 x) ?_
  have := h1 (Rpath x)
  have hxx : Rpath (Rpath x) = x := by ext1 t; exact RV_RV (x t)
  rwa [hxx] at this

theorem Rpath_add {T : ℝ} (x y : C(Icc (0 : ℝ) T, V1)) : Rpath (x + y) = Rpath x + Rpath y := by
  ext1 t; exact RV_add (x t) (y t)

theorem Rpath_heatPath {ν T : ℝ} (hν : 0 < ν) (a₀ : V1) :
    Rpath (heatPath hν a₀ : C(Icc (0 : ℝ) T, V1)) = heatPath hν (RV a₀) := by
  ext1 t; exact RV_heatOp ν t a₀

theorem Rpath_duhamelPath {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (x y : C(Icc (0 : ℝ) T, V1)) :
    Rpath (duhamelPath hν hT x y) = duhamelPath hν hT (Rpath x) (Rpath y) := by
  ext1 t
  rw [Rpath_apply, duhamelPath_apply, duhamelPath_apply, duhamel, duhamel, ← RVL_apply,
    ← RVL.integral_comp_comm (integrable_duhIntegrand hν hT x y t)]
  refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
  show RVL (duhIntegrand ν hT x y t σ) = duhIntegrand ν hT (Rpath x) (Rpath y) t σ
  unfold duhIntegrand
  by_cases hσ : σ ∈ Iic (t : ℝ)
  · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ, RVL_apply, RV_kernelOp,
      RW_tensorConv]
    rfl
  · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ, map_zero]

/-! ## Invariance of the fixed point -/

theorem fixedPoint_unique_radius {X : Type*} [NormedAddCommGroup X] {B : X → X → X} {C R : ℝ}
    (hC : 0 < C) (hB : ∀ a b : X, ‖B a b‖ ≤ C * (‖a‖ * ‖b‖))
    (hdiff : ∀ a b : X, B a a - B b b = B (a - b) a + B b (a - b)) (hCR : 2 * C * R < 1)
    (y : X) {x z : X} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hxe : x = y + B x x) (hze : z = y + B z z) : x = z := by
  have hd : x - z = B (x - z) x + B z (x - z) := by
    rw [← hdiff]; conv_lhs => rw [hxe, hze]
    abel
  have hn : ‖x - z‖ ≤ (2 * C * R) * ‖x - z‖ := by
    have h := (norm_add_le (B (x - z) x) (B z (x - z))).trans (add_le_add (hB _ _) (hB _ _))
    rw [← hd] at h
    have hab : (0 : ℝ) ≤ ‖x - z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hC.le hab),
      mul_le_mul_of_nonneg_left hz (mul_nonneg hC.le hab)]
  have h0 : ‖x - z‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖x - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **The Picard fixed point of a reflection-invariant datum is
reflection-invariant.** -/
theorem Rpath_fixed {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν) (ha : RV a₀ = a₀) (x : C(Icc (0 : ℝ) T, V1))
    (hx : ‖x‖ ≤ 2 * ‖a₀‖) (hxeq : x = heatPath hν a₀ + duhamelPath hν hT.le x x) :
    Rpath x = x := by
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T with hC
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hC0 : 0 < C := by rw [hC]; positivity
  have hroot : 100 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [show (10 : ℝ) ^ 4 * T * ‖a₀‖ ^ 2 = (100 * (Real.sqrt T * ‖a₀‖)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]; ring,
      Real.sqrt_sq (by positivity)] at h
  have hCR : 2 * C * (2 * ‖a₀‖) < 1 := by
    have heq : 2 * C * (2 * ‖a₀‖) = 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν := by
      rw [hC]; field_simp; ring
    rw [heq, div_lt_one hsν]
    have : 0 ≤ Real.sqrt T * ‖a₀‖ := by positivity
    nlinarith
  have hRx : Rpath x = heatPath hν a₀ + duhamelPath hν hT.le (Rpath x) (Rpath x) := by
    conv_lhs => rw [hxeq]
    rw [Rpath_add, Rpath_heatPath, ha, Rpath_duhamelPath]
  exact fixedPoint_unique_radius hC0 (norm_duhamelPath_le hν hT.le) (duhamelPath_diff hν hT.le)
    hCR _ ((norm_Rpath x).le.trans hx) hx hRx hxeq

/-! ## The inverse Fourier transform of an invariant class is real -/

theorem conj_fourierInv_of_Rc {f : L1C} (hf : Rc f = f) (y : ES) :
    conj (𝓕⁻ (⇑f) y) = 𝓕⁻ (⇑f) y := by
  rw [conj_fourierInv]
  refine fourierInv_congr ?_ y
  have h := coeFn_Rc f
  rw [hf] at h
  exact h.symm

/-! ## Hermitian symmetry of real Schwartz data -/

open Navier.Analysis.ContinuousLeiLinPhysicalCarrier Navier.Analysis.FourierMajorant
  Navier.Analysis.WienerSchwartzLocal in
theorem reflC_fourierDatum (u₀ : Navier.SchwartzVelocity) (i : Fin 3) :
    reflC (fun ξ => fourierDatum u₀ ξ i) = fun ξ => fourierDatum u₀ ξ i := by
  funext ξ
  set g : ES → ℂ := ⇑(euclidComponent u₀ i) with hg
  have hreal : ∀ y, conj (g y) = g y := fun y => by
    rw [hg, euclidComponent_apply, Complex.conj_ofReal]
  have hF : ∀ η, fourierDatum u₀ η i = 𝓕 g η := fun η => by
    show 𝓕 (euclidComponent u₀ i) η = 𝓕 g η
    rw [SchwartzMap.fourier_coe]
  simp only [reflC, hF]
  rw [← Real.fourierInv_eq_fourier_neg, conj_fourierInv, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun x => reflC g (-x)) = g := by
    funext y; simp [reflC, hreal]
  rw [hfun]

open Navier.Analysis.WienerSchwartzLocal in
theorem RV_wienerDatum (u₀ : Navier.SchwartzVelocity) : RV (wienerDatum u₀) = wienerDatum u₀ := by
  funext i
  apply Lp.ext
  filter_upwards [coeFn_Rc (wienerDatum u₀ i), reflC_congr (coeFn_wienerDatum u₀ i),
    coeFn_wienerDatum u₀ i] with ξ h1 h2 h3
  rw [show RV (wienerDatum u₀) i = Rc (wienerDatum u₀ i) from rfl, h1, h2, h3]
  exact congrFun (reflC_fourierDatum u₀ i) ξ

/-! ## Consumer: the smooth local solution is real -/

open Navier.Analysis.ContinuousLeiLinPhysicalCarrier Navier.Analysis.ContinuousLeiLinSelfMap
  Navier.Analysis.WienerSchwartzLocal Navier.Analysis.WienerSchwartzSmooth in
/-- **Large-data local solution from Schwartz data: jointly `C^∞` and real.**
In addition to `exists_smooth_wienerSolution`, every physical coordinate is
real-valued on `[0, T] × ℝ³`. -/
theorem exists_real_smooth_wienerSolution {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (u₀ : Navier.SchwartzVelocity) (hsmall : 10 ^ 4 * T * ‖wienerDatum u₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1), ‖x‖ ≤ 2 * ‖wienerDatum u₀‖ ∧
      x = heatPath hν (wienerDatum u₀) + duhamelPath hν hT.le x x ∧
      ∃ w : ℝ → ES → ComplexSpace,
        (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
          (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i)) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES,
          w t ξ = continuousMildImage ν hν (fourierDatum u₀) w t ξ) ∧
        Navier.Analysis.WienerPointwiseODE.Good T w ∧
        (∀ i : Fin 3, ContDiffOn ℝ ∞ (fun z : ℝ × ES => physicalCoord (w z.1) i z.2)
          (Ico (0 : ℝ) T ×ˢ (univ : Set ES))) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ (i : Fin 3) (y : ES),
          conj (physicalCoord (w t) i y) = physicalCoord (w t) i y) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3,
          ∀ᵐ ξ ∂(volume : Measure ES), w t (-ξ) i = conj (w t ξ i) := by
  obtain ⟨x, hxle, hxeq, w, hw, hfix, hG, hsm⟩ := exists_smooth_wienerSolution hν hT u₀ hsmall
  have hR : Rpath x = x := Rpath_fixed hν hT (wienerDatum u₀) hsmall (RV_wienerDatum u₀) x
    hxle hxeq
  have hRt : ∀ t (ht : t ∈ Icc (0 : ℝ) T) i, Rc (x ⟨t, ht⟩ i) = x ⟨t, ht⟩ i := by
    intro t ht i
    have h := congrArg (fun z : C(Icc (0 : ℝ) T, V1) => z ⟨t, ht⟩ i) hR
    exact h
  refine ⟨x, hxle, hxeq, w, hw, hfix, hG, hsm, fun t ht i y => ?_, fun t ht i => ?_⟩
  · unfold physicalCoord
    rw [fourierInv_congr (hw t ht i) y]
    exact conj_fourierInv_of_Rc (hRt t ht i) y
  · have h1 := coeFn_Rc (x ⟨t, ht⟩ i)
    rw [hRt t ht i] at h1
    filter_upwards [hw t ht i, ae_neg (hw t ht i), h1] with ξ ha hb hc
    rw [hb, ha, hc]
    simp [reflC]

end Navier.Analysis.WienerReality

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerReality.exists_real_smooth_wienerSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerReality.Rpath_fixed
