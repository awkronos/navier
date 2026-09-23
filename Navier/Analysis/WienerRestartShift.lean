import Navier.Analysis.WienerGevrey

/-!
# Restarting the Wiener mild solution at a positive time

The Fourier mild equation has the semigroup property: if `x` solves it on `[0, T]` with
datum `a₀`, then `s ↦ x(t₁ + s)` solves it on `[0, T - t₁]` with datum `x(t₁)`
(`shiftPath_fixed`).  Combined with instant Gevrey smoothing
(`WienerGevrey.fixedPoint_mem_gevSet`), the restarted path carries every Fourier moment
uniformly on `[0, T - t₁]` (`shiftPath_mem_momSet`), with no moment of `a₀` assumed.

This is step 2 of item 6: data with Fourier transform in `L¹` (for instance `H³` data)
reach, after an arbitrarily short time, the moment class on which the repository's
smoothness, pressure, energy and `R`-regularity theory for Wiener solutions is built.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Navier.Analysis.WienerRestartShift

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerMoments
open Navier.Analysis.WienerGevrey

/-! ## Semigroup identities for the multipliers -/

theorem mulL_mulL (m m' m'' : LinfC) (h : ∀ᵐ ξ ∂(volume : Measure ES), m ξ * m' ξ = m'' ξ)
    (f : L1C) : mulL m (mulL m' f) = mulL m'' f := by
  apply Lp.ext
  filter_upwards [coeFn_mulL m (mulL m' f), coeFn_mulL m' f, coeFn_mulL m'' f, h] with
    ξ h1 h2 h3 h4
  rw [h1, h2, h3, ← h4, mul_assoc]

theorem heatFactor_add (ν s t : ℝ) (ξ : ES) :
    heatFactor ν s ξ * heatFactor ν t ξ = heatFactor ν (s + t) ξ := by
  unfold heatFactor
  rw [← Real.exp_add]
  congr 1
  ring

theorem heatOp_heatOp {ν s t : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (ht : 0 ≤ t) (v : V1) :
    heatOp ν s (heatOp ν t v) = heatOp ν (s + t) v := by
  funext i
  simp only [heatOp_apply]
  refine mulL_mulL _ _ _ ?_ _
  filter_upwards [coeFn_heatLinf hν s, coeFn_heatLinf hν t, coeFn_heatLinf hν (s + t)] with
    ξ h1 h2 h3
  rw [h1, h2, h3, max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht),
    ← Complex.ofReal_mul, heatFactor_add]

theorem heatOp_kernelOp {ν s σ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hσ : 0 < σ) (W : W1) :
    heatOp ν s (kernelOp ν σ W) = kernelOp ν (s + σ) W := by
  funext i
  rw [heatOp_apply]
  unfold kernelOp
  rw [tensorMulOp_apply, tensorMulOp_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine mulL_mulL _ _ _ ?_ _
  filter_upwards [coeFn_heatLinf hν.le s, coeFn_kernelLinf hν hσ i j k,
    coeFn_kernelLinf hν (add_pos_of_nonneg_of_pos hs hσ) i j k] with ξ h1 h2 h3
  rw [h1, h2, h3, max_eq_left hs]
  unfold kernelSymbol
  rw [← mul_assoc, ← Complex.ofReal_mul, heatFactor_add]

/-! ## The shift identity for the mild equation -/

variable {ν T : ℝ}

/-- The nonlinearity at time `r`. -/
def nl (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) (r : ℝ) : W1 :=
  tensorConv (extend hT0 y r) (extend hT0 y r)

theorem integrableOn_kernel_nl (hν : 0 < ν) (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) {t : ℝ}
    (htT : t ≤ T) :
    IntegrableOn (fun σ => kernelOp ν σ (nl hT0 y (t - σ))) (Ioc 0 t) := by
  have h := (show IntegrableOn (duhIntegrand ν hT0 y y t) (Ioc 0 T) volume from
    integrable_duhIntegrand hν hT0 y y t).mono_set (Ioc_subset_Ioc_right htT)
  refine IntegrableOn.congr_fun h (fun σ hσ => ?_) measurableSet_Ioc
  unfold duhIntegrand
  exact Set.indicator_of_mem (show σ ∈ Iic t from hσ.2) _

/-- The pointwise mild equation of a Picard fixed point. -/
theorem mild_of_fixed (hν : 0 < ν) (hT : 0 < T) (a₀ : V1) (y : C(Icc (0 : ℝ) T, V1))
    (hyeq : y = heatPath hν a₀ + duhamelPath hν hT.le y y) (t : Icc (0 : ℝ) T) :
    y t = heatOp ν t a₀ + ∫ σ in Ioc 0 (t : ℝ), kernelOp ν σ (nl hT.le y (t - σ)) := by
  have := congrArg (fun z : C(Icc (0 : ℝ) T, V1) => z t) hyeq
  simp only [ContinuousMap.add_apply] at this
  rw [this, duhamelPath_apply, duhamel_eq_causal hT.le y y t.2.2]
  rfl

/-- **The semigroup identity of the mild equation.** -/
theorem mild_shift (hν : 0 < ν) (hT : 0 < T) (a₀ : V1) (y : C(Icc (0 : ℝ) T, V1))
    (hyeq : y = heatPath hν a₀ + duhamelPath hν hT.le y y) {t₁ s : ℝ} (h1 : 0 ≤ t₁)
    (hs : 0 ≤ s) (hts : t₁ + s ≤ T) :
    y ⟨t₁ + s, by constructor <;> linarith⟩ = heatOp ν s (y ⟨t₁, ⟨h1, by linarith⟩⟩) +
      ∫ σ in Ioc 0 s, kernelOp ν σ (nl hT.le y (t₁ + s - σ)) := by
  set F : ℝ → V1 := fun σ => kernelOp ν σ (nl hT.le y (t₁ + s - σ)) with hF
  set G : ℝ → V1 := fun σ => kernelOp ν σ (nl hT.le y (t₁ - σ)) with hG
  have hFi : IntegrableOn F (Ioc 0 (t₁ + s)) := integrableOn_kernel_nl hν hT.le y hts
  have hGi : IntegrableOn G (Ioc 0 t₁) := integrableOn_kernel_nl hν hT.le y (by linarith)
  have hA := mild_of_fixed hν hT a₀ y hyeq ⟨t₁ + s, by constructor <;> linarith⟩
  have hB := mild_of_fixed hν hT a₀ y hyeq ⟨t₁, ⟨h1, by linarith⟩⟩
  simp only at hA hB
  rw [hA, hB, map_add, heatOp_heatOp hν.le hs h1, add_comm s t₁]
  rw [add_assoc]
  congr 1
  -- interval form
  have hFI : IntervalIntegrable F volume 0 (t₁ + s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr hFi
  have hF1 : IntervalIntegrable F volume 0 s := hFI.mono_set (by
    rw [uIcc_of_le hs, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have hF2 : IntervalIntegrable F volume s (t₁ + s) := hFI.mono_set (by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc hs le_rfl)
  have hGI : IntervalIntegrable G volume 0 t₁ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h1).mpr hGi
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ t₁ + s),
    ← intervalIntegral.integral_of_le hs, ← intervalIntegral.integral_of_le h1,
    ← intervalIntegral.integral_add_adjacent_intervals hF1 hF2]
  rw [← (heatOp ν s).intervalIntegral_comp_comm hGI, add_comm]
  congr 1
  -- the tail, translated
  have htr : ∫ σ in s..t₁ + s, F σ = ∫ σ in (0 : ℝ)..t₁, F (σ + s) := by
    rw [intervalIntegral.integral_comp_add_right F s, zero_add]
  rw [htr]
  refine intervalIntegral.integral_congr_ae ?_
  refine Eventually.of_forall fun σ hσ => ?_
  rw [uIoc_of_le h1] at hσ
  simp only [hF, hG]
  rw [heatOp_kernelOp hν hs hσ.1, add_comm s σ]
  congr 2
  ring

/-! ## The restarted path -/

/-- The path `s ↦ y(t₁ + s)` on `[0, T - t₁]`. -/
def shiftPath (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) (t₁ : ℝ) :
    C(Icc (0 : ℝ) (T - t₁), V1) :=
  ⟨fun s => extend hT0 y (t₁ + s),
    (continuous_extend hT0 y).comp (continuous_const.add continuous_subtype_val)⟩

theorem shiftPath_apply (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) (t₁ : ℝ)
    (s : Icc (0 : ℝ) (T - t₁)) : shiftPath hT0 y t₁ s = extend hT0 y (t₁ + s) := rfl

theorem extend_eq (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    extend hT0 y t = y ⟨t, ht⟩ := by
  unfold WienerLocalMild.extend; rw [projIcc_of_mem hT0 ht]

theorem norm_shiftPath_le (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1)) (t₁ : ℝ) :
    ‖shiftPath hT0 y t₁‖ ≤ ‖y‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun _ => norm_extend_le hT0 y _

/-- **The restarted path solves the mild equation with datum `y(t₁)`.** -/
theorem shiftPath_fixed (hν : 0 < ν) (hT : 0 < T) (a₀ : V1) (y : C(Icc (0 : ℝ) T, V1))
    (hyeq : y = heatPath hν a₀ + duhamelPath hν hT.le y y) {t₁ : ℝ} (h1 : 0 ≤ t₁)
    (h1T : t₁ < T) :
    shiftPath hT.le y t₁ = heatPath hν (y ⟨t₁, ⟨h1, h1T.le⟩⟩) +
      duhamelPath hν (sub_pos.mpr h1T).le (shiftPath hT.le y t₁) (shiftPath hT.le y t₁) := by
  set hT' : 0 ≤ T - t₁ := (sub_pos.mpr h1T).le
  ext1 s
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hsT : t₁ + s ≤ T := by linarith [s.2.2]
  rw [shiftPath_apply, extend_eq hT.le y ⟨by linarith, hsT⟩,
    mild_shift hν hT a₀ y hyeq h1 hs0 hsT]
  simp only [ContinuousMap.add_apply, duhamelPath_apply]
  rw [duhamel_eq_causal hT' _ _ s.2.2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
  show kernelOp ν σ (nl hT.le y (t₁ + s - σ)) =
    kernelOp ν σ (tensorConv (extend hT' (shiftPath hT.le y t₁) (s - σ))
      (extend hT' (shiftPath hT.le y t₁) (s - σ)))
  have hm : s - σ ∈ Icc (0 : ℝ) (T - t₁) := ⟨by linarith [hσ.2], by linarith [hσ.1, s.2.2]⟩
  rw [extend_eq hT' _ hm, shiftPath_apply]
  unfold nl
  rw [show t₁ + (s : ℝ) - σ = t₁ + ((s : ℝ) - σ) by ring]

/-! ## Every moment on the restarted path -/

/-- **Uniform moments after an arbitrarily short time.**  If `10⁶ T ‖a₀‖² ≤ ν` and `x` is
a Picard fixed point in the ball `2‖a₀‖`, then for every `t₁ ∈ (0, T)` the restarted
path `s ↦ x(t₁ + s)` is the Picard fixed point with datum `x(t₁)` on `[0, T - t₁]` and
carries every Fourier moment uniformly: `momV n ≤ 2mₙ e^{γₙ s}` with
`mₙ = n! (νt₁)^{-n/2} · 12‖a₀‖`. -/
theorem shiftPath_mem_momSet (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 6 * T * ‖a₀‖ ^ 2 ≤ ν) (x : C(Icc (0 : ℝ) T, V1))
    (hxle : ‖x‖ ≤ 2 * ‖a₀‖) (hxeq : x = heatPath hν a₀ + duhamelPath hν hT.le x x)
    {t₁ : ℝ} (h1 : 0 < t₁) (h1T : t₁ < T) (n : ℕ) :
    shiftPath hT.le x t₁ ∈ momSet (T := T - t₁) n
      (2 * ((Nat.factorial n : ℝ) / Real.sqrt (ν * t₁) ^ n * (12 * ‖a₀‖)))
      (momRate ν n (x ⟨t₁, ⟨h1.le, h1T.le⟩⟩)) := by
  set T' := T - t₁ with hT'
  have hT'0 : 0 < T' := sub_pos.mpr h1T
  set b := x ⟨t₁, ⟨h1.le, h1T.le⟩⟩ with hb
  have hbn : ‖b‖ ≤ 2 * ‖a₀‖ := (x.norm_coe_le_norm _).trans hxle
  have hsmall' : 10 ^ 4 * T' * ‖b‖ ^ 2 ≤ ν := by
    have h2 : ‖b‖ ^ 2 ≤ 4 * ‖a₀‖ ^ 2 := by nlinarith [norm_nonneg b]
    have h3 : T' ≤ T := by rw [hT']; linarith
    have h4 : 10 ^ 4 * T' * ‖b‖ ^ 2 ≤ 10 ^ 4 * T * (4 * ‖a₀‖ ^ 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h3 (by norm_num)) h2 (sq_nonneg _)
      positivity
    nlinarith [sq_nonneg ‖a₀‖]
  obtain ⟨x', hx'le, hx'eq, hmom⟩ := exists_wienerMildSolution_moments hν hT'0 b hsmall'
  -- the restarted path is that fixed point
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T' with hC
  have hC0 : 0 < C := by rw [hC]; have := Real.sqrt_pos.mpr hT'0; positivity
  have hroot : 1000 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν :=
    sqrt_small_of hT (by norm_num) ‖a₀‖ (norm_nonneg _) (by norm_num at hsmall ⊢; linarith)
  have hsT' : Real.sqrt T' ≤ Real.sqrt T := Real.sqrt_le_sqrt (by rw [hT']; linarith)
  have hR : 2 * C * (4 * ‖a₀‖) < 1 := by
    have h1' : 2 * C * (4 * ‖a₀‖) = 144 * (Real.sqrt T' * ‖a₀‖) / Real.sqrt ν := by
      rw [hC]; field_simp; ring
    rw [h1', div_lt_one hsν]
    have : Real.sqrt T' * ‖a₀‖ ≤ Real.sqrt T * ‖a₀‖ :=
      mul_le_mul_of_nonneg_right hsT' (norm_nonneg _)
    have h0 : 0 ≤ Real.sqrt T' * ‖a₀‖ := by positivity
    by_cases hz : Real.sqrt T * ‖a₀‖ = 0
    · have : Real.sqrt T' * ‖a₀‖ = 0 := le_antisymm (by linarith) h0
      rw [this]; linarith
    · have hpos : 0 < Real.sqrt T * ‖a₀‖ := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      nlinarith
  have heq : shiftPath hT.le x t₁ = x' :=
    picard_unique_R hC0 (norm_duhamelPath_le hν hT'0.le) (duhamelPath_diff hν hT'0.le) hR
      ((norm_shiftPath_le hT.le x t₁).trans (by linarith [norm_nonneg a₀]))
      (hx'le.trans (by linarith))
      (shiftPath_fixed hν hT a₀ x hxeq h1.le h1T) hx'eq
  rw [heq]
  refine hmom n _ (by positivity) ?_
  have hg := fixedPoint_mem_gevSet hν hT a₀ hsmall x hxle hxeq
  have := momV_le_of_gevSet hg hν n ⟨t₁, ⟨h1.le, h1T.le⟩⟩ h1
  rwa [← ENNReal.ofReal_mul (by positivity)] at this

end Navier.Analysis.WienerRestartShift

set_option pp.fullNames true in
#check @Navier.Analysis.WienerRestartShift.shiftPath_mem_momSet
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartShift.shiftPath_mem_momSet
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartShift.shiftPath_fixed
