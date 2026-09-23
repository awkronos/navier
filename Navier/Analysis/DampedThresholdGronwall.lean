import Mathlib

/-!
# The threshold Gronwall lemma behind the T-uniform continuation estimate

Abstract form of the damped `Hˢ` argument (OPEN_FRONTIER_MAP row A, (P) verdict):
`Z = log(1 + ‖Λˢu‖)` may grow only while it lies above a threshold `Λ`, and there
at rate `a(t)(c + Z)` with `a ≥ 0` the (cut-off) vorticity rate, whose running
integral `A` stays below the BKM budget `M`.  Below the threshold nothing is
assumed.  Conclusion: `Z(t) ≤ (c + max(Z 0, Λ)) e^{A(t)} - c ≤ (c + max(Z 0, Λ)) e^{M} - c`,
uniformly in the horizon.
-/

set_option autoImplicit false

open Set Filter Topology

namespace Navier.Analysis.DampedThresholdGronwall

/-- **Threshold Gronwall.** -/
theorem threshold_gronwall {Z Z' A a : ℝ → ℝ} {T Λ c : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ)
    (hZc : ContinuousOn Z (Icc 0 T))
    (hZd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hAc : ContinuousOn A (Icc 0 T))
    (hAd : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (a t) (Ici t) t)
    (hA0 : A 0 = 0) (ha : ∀ t ∈ Ico 0 T, 0 ≤ a t)
    (hineq : ∀ t ∈ Ico 0 T, Λ < Z t → Z' t ≤ a t * (c + Z t)) :
    ∀ t ∈ Icc 0 T, Z t ≤ (c + max (Z 0) Λ) * Real.exp (A t) - c := by
  set K : ℝ := max (Z 0) Λ with hK
  have hK0 : 0 ≤ K := le_trans hΛ (le_max_right _ _)
  -- the running integral is nonnegative
  have hApos : ∀ t ∈ Icc 0 T, 0 ≤ A t := by
    have h := image_le_of_deriv_right_le_deriv_boundary (f := fun t => -A t) (f' := fun t => -a t)
      (a := 0) (b := T) hAc.neg (fun t ht => (hAd t ht).neg) (B := fun _ => 0) (B' := fun _ => 0)
      (by simp [hA0]) continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _)
      (fun t ht => by simp only [Left.neg_nonpos_iff]; exact ha t ht)
    intro t ht
    have := h ht
    linarith
  -- the strict barriers
  have key : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc 0 T,
      Z t ≤ (c + K + ε) * Real.exp (A t + ε * t) - c := by
    intro ε hε
    have hB : ContinuousOn (fun t => (c + K + ε) * Real.exp (A t + ε * t) - c) (Icc 0 T) :=
      ((continuousOn_const.mul ((hAc.add (continuousOn_const.mul continuousOn_id)).rexp)).sub
        continuousOn_const)
    have hBd : ∀ t ∈ Ico 0 T, HasDerivWithinAt
        (fun t => (c + K + ε) * Real.exp (A t + ε * t) - c)
        ((c + K + ε) * (Real.exp (A t + ε * t) * (a t + ε))) (Ici t) t := by
      intro t ht
      have h1 : HasDerivWithinAt (fun t => A t + ε * t) (a t + ε) (Ici t) t := by
        have h2 : HasDerivWithinAt (fun t : ℝ => ε * t) ε (Ici t) t := by
          simpa using (hasDerivWithinAt_id t (Ici t)).const_mul ε
        exact (hAd t ht).fun_add h2
      exact (h1.exp.const_mul (c + K + ε)).sub_const c
    refine image_le_of_deriv_right_lt_deriv_boundary' hZc hZd ?_ hB hBd ?_
    · simp only [hA0, mul_zero, add_zero, Real.exp_zero, mul_one]
      have : Z 0 ≤ K := le_max_left _ _
      linarith
    · intro t ht heq
      have htI : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hE : 1 ≤ Real.exp (A t + ε * t) := by
        rw [Real.one_le_exp_iff]
        have := hApos t htI
        have := ht.1
        positivity
      have hpos : 0 < (c + K + ε) * Real.exp (A t + ε * t) := by positivity
      have hZt : Λ < Z t := by
        rw [heq]
        have : c + K + ε ≤ (c + K + ε) * Real.exp (A t + ε * t) := by nlinarith
        have : Λ ≤ K := le_max_right _ _
        linarith
      have h1 := hineq t ht hZt
      rw [heq] at h1
      have h2 : a t * (c + ((c + K + ε) * Real.exp (A t + ε * t) - c)) <
          (c + K + ε) * (Real.exp (A t + ε * t) * (a t + ε)) := by
        have : a t * (c + ((c + K + ε) * Real.exp (A t + ε * t) - c)) =
            a t * ((c + K + ε) * Real.exp (A t + ε * t)) := by ring
        rw [this]
        nlinarith [ha t ht]
      exact lt_of_le_of_lt h1 h2
  intro t ht
  have hlim : Tendsto (fun ε : ℝ => (c + K + ε) * Real.exp (A t + ε * t) - c) (𝓝[>] 0)
      (𝓝 ((c + K) * Real.exp (A t) - c)) := by
    have hcont : Continuous (fun ε : ℝ => (c + K + ε) * Real.exp (A t + ε * t) - c) := by
      fun_prop
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε t ht

/-- **T-uniform form**: with the running integral bounded by the budget `M`. -/
theorem threshold_gronwall_uniform {Z Z' A a : ℝ → ℝ} {T Λ c M : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ)
    (hZc : ContinuousOn Z (Icc 0 T))
    (hZd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hAc : ContinuousOn A (Icc 0 T))
    (hAd : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (a t) (Ici t) t)
    (hA0 : A 0 = 0) (ha : ∀ t ∈ Ico 0 T, 0 ≤ a t) (hAM : ∀ t ∈ Icc 0 T, A t ≤ M)
    (hineq : ∀ t ∈ Ico 0 T, Λ < Z t → Z' t ≤ a t * (c + Z t)) :
    ∀ t ∈ Icc 0 T, Z t ≤ (c + max (Z 0) Λ) * Real.exp M - c := by
  intro t ht
  have h := threshold_gronwall hc hΛ hZc hZd hAc hAd hA0 ha hineq t ht
  have hK : 0 ≤ c + max (Z 0) Λ := add_nonneg hc (le_trans hΛ (le_max_right _ _))
  have := Real.exp_le_exp.mpr (hAM t ht)
  nlinarith

/-! ## The pointwise damped rate reduction -/

theorem mul_log_one_add_inv_le {y : ℝ} (hy : 0 ≤ y) : y * Real.log (1 + 1 / y) ≤ 1 := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  have h1 : Real.log (1 + 1 / y) ≤ 1 / y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / y by positivity)
    linarith
  calc y * Real.log (1 + 1 / y) ≤ y * (1 / y) := mul_le_mul_of_nonneg_left h1 h.le
    _ = 1 := by field_simp

theorem log_one_add_div_le {y X : ℝ} (hy : 0 < y) (hX : 0 ≤ X) :
    Real.log (1 + X / y) ≤ Real.log (1 + X) + Real.log (1 + 1 / y) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have e : (1 + X) * (1 + 1 / y) = 1 + X / y + (X + 1 / y) := by field_simp; ring
  have : 0 ≤ X + 1 / y := by positivity
  linarith

/-- **The damped rate reduction.**  With `θ > 0` the interpolation exponent
(`θ = 2/s`), the log-Sobolev growth rate `C y (1 + log(1 + Y/y) + log(1 + E/y)) Y`
is dominated by the dissipation `ν E^{-θ} Y^{θ} Y` above a threshold `L` whenever
the vorticity level `y` is below `η`; above `η` it is at most
`C y (c_η + log(1+Y)) (1+Y)`. -/
theorem damped_rate_reduction {C ν E η θ : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hE : 0 < E)
    (hη : 0 < η) (hθ : 0 < θ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ y Y : ℝ, 0 ≤ y → L ≤ Y →
      C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) * Y -
          ν * E ^ (-θ) * Y ^ θ * Y ≤
        (if η ≤ y then
          C * y * ((1 + Real.log (1 + 1 / η) + Real.log (1 + E / η)) + Real.log (1 + Y)) * (1 + Y)
        else 0) := by
  set κ : ℝ := ν * E ^ (-θ) with hκ
  have hκ0 : 0 < κ := by positivity
  set α : ℝ := C * (η * (1 + Real.log 2 + Real.log (1 + E)) + 2) with hα
  -- eventually `α + Cη log Y ≤ κ Y^θ`
  have hlog : ∀ᶠ Y in atTop, C * η * Real.log Y ≤ κ / 2 * Y ^ θ := by
    have ho := (isLittleO_log_rpow_atTop hθ).bound (show 0 < κ / 2 / (C * η + 1) by positivity)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with Y hY h1
    have hlY : 0 ≤ Real.log Y := Real.log_nonneg h1
    have hYθ : 0 ≤ Y ^ θ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hlY, Real.norm_eq_abs, abs_of_nonneg hYθ] at hY
    have hCη : 0 ≤ C * η := by positivity
    calc C * η * Real.log Y ≤ C * η * (κ / 2 / (C * η + 1) * Y ^ θ) :=
          mul_le_mul_of_nonneg_left hY hCη
      _ ≤ κ / 2 * Y ^ θ := by
          rw [show C * η * (κ / 2 / (C * η + 1) * Y ^ θ) =
            (C * η / (C * η + 1)) * (κ / 2 * Y ^ θ) by field_simp]
          have : C * η / (C * η + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
          have : 0 ≤ κ / 2 * Y ^ θ := by positivity
          nlinarith
  have hpow : ∀ᶠ Y in atTop, α ≤ κ / 2 * Y ^ θ := by
    have := (tendsto_rpow_atTop hθ).const_mul_atTop (show 0 < κ / 2 by positivity)
    exact this.eventually_ge_atTop α
  obtain ⟨L, hL⟩ := eventually_atTop.mp ((hlog.and hpow).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max L 1, le_max_right _ _, fun y Y hy hLY => ?_⟩
  obtain ⟨⟨h1, h2⟩, hY1⟩ := hL Y (le_trans (le_max_left _ _) hLY)
  have hY0 : 0 ≤ Y := by linarith
  have hl1 : 0 ≤ Real.log (1 + Y) := Real.log_nonneg (by linarith)
  split_ifs with hyη
  · -- high vorticity
    have hy0 : 0 < y := lt_of_lt_of_le hη hyη
    have e1 : Real.log (1 + Y / y) ≤ Real.log (1 + Y) + Real.log (1 + 1 / η) := by
      refine (log_one_add_div_le hy0 hY0).trans (add_le_add le_rfl ?_)
      refine Real.log_le_log (by positivity) ?_
      have : 1 / y ≤ 1 / η := one_div_le_one_div_of_le hη hyη
      linarith
    have e2 : Real.log (1 + E / y) ≤ Real.log (1 + E / η) := by
      refine Real.log_le_log (by positivity) ?_
      have : E / y ≤ E / η := div_le_div_of_nonneg_left hE.le hη hyη
      linarith
    have hdiss : 0 ≤ κ * Y ^ θ * Y := by positivity
    have hCy : 0 ≤ C * y := by positivity
    calc C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) * Y - ν * E ^ (-θ) * Y ^ θ * Y
        ≤ C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) * Y := by
          have : ν * E ^ (-θ) * Y ^ θ * Y = κ * Y ^ θ * Y := by rw [hκ]
          linarith
      _ ≤ C * y * ((1 + Real.log (1 + 1 / η) + Real.log (1 + E / η)) + Real.log (1 + Y)) * Y := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCy) hY0
          linarith
      _ ≤ C * y * ((1 + Real.log (1 + 1 / η) + Real.log (1 + E / η)) + Real.log (1 + Y)) *
            (1 + Y) := by
          have : 0 ≤ Real.log (1 + 1 / η) := Real.log_nonneg (by
            have : 0 ≤ 1 / η := by positivity
            linarith)
          have : 0 ≤ Real.log (1 + E / η) := Real.log_nonneg (by
            have : 0 ≤ E / η := by positivity
            linarith)
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          positivity
  · -- low vorticity: the dissipation wins
    push_neg at hyη
    have hbound : C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) ≤
        α + C * η * Real.log Y := by
      rcases hy.eq_or_lt with h0 | hy0
      · subst h0
        simp only [mul_zero, zero_mul]
        have : 0 ≤ Real.log Y := Real.log_nonneg hY1
        have : 0 ≤ α := by
          have : 0 ≤ Real.log (1 + E) := Real.log_nonneg (by linarith)
          have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          positivity
        have : 0 ≤ C * η * Real.log Y := by positivity
        linarith
      have f1 := log_one_add_div_le hy0 hY0
      have f2 := log_one_add_div_le hy0 hE.le
      have g := mul_log_one_add_inv_le hy
      have hY2 : Real.log (1 + Y) ≤ Real.log 2 + Real.log Y := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by linarith) (by linarith)
      have hlY : 0 ≤ Real.log (1 + Y) := hl1
      have hlE : 0 ≤ Real.log (1 + E) := Real.log_nonneg (by linarith)
      have hl1y : 0 ≤ Real.log (1 + 1 / y) := Real.log_nonneg (by
        have : 0 ≤ 1 / y := by positivity
        linarith)
      -- y * (...) ≤ η (1 + log(1+Y) + log(1+E)) + 2
      have key : y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) ≤
          η * (1 + Real.log 2 + Real.log (1 + E)) + 2 + η * Real.log Y := by
        have t1 : y * Real.log (1 + Y / y) ≤ y * Real.log (1 + Y) + 1 := by
          nlinarith [mul_le_mul_of_nonneg_left f1 hy]
        have t2 : y * Real.log (1 + E / y) ≤ y * Real.log (1 + E) + 1 := by
          nlinarith [mul_le_mul_of_nonneg_left f2 hy]
        have t3 : y * (1 + Real.log (1 + Y) + Real.log (1 + E)) ≤
            η * (1 + Real.log (1 + Y) + Real.log (1 + E)) :=
          mul_le_mul_of_nonneg_right hyη.le (by positivity)
        nlinarith
      calc C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y))
          = C * (y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y))) := by ring
        _ ≤ C * (η * (1 + Real.log 2 + Real.log (1 + E)) + 2 + η * Real.log Y) :=
            mul_le_mul_of_nonneg_left key hC
        _ = α + C * η * Real.log Y := by rw [hα]; ring
    have hsum : C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) ≤ κ * Y ^ θ := by
      linarith
    have : C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) * Y ≤ κ * Y ^ θ * Y :=
      mul_le_mul_of_nonneg_right hsum hY0
    linarith

end Navier.Analysis.DampedThresholdGronwall

set_option pp.fullNames true in
#print axioms Navier.Analysis.DampedThresholdGronwall.threshold_gronwall_uniform
set_option pp.fullNames true in
#print axioms Navier.Analysis.DampedThresholdGronwall.damped_rate_reduction
