/-
Original work, lane L6b3, 2026-09-14.
-/
import Navier.Analysis.BKMProfileGronwallPair

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators ContDiff
open Navier Navier.Analysis.BKMProfileGronwallPair
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate

/-!
# Scalar leaf-generators for the named residual `VorticityRateBound`

`Navier.Analysis.BKMProfileGronwallPair` reduces the BKM residual for the
selected forced profile `u` to exactly one scalar estimate on the peak-vorticity
profile `V u`:

    VorticityRateBound u :∃ C₂ ≥ 0, ∀ t ∈ Ico 0 1,
      V u t ≤ C₂ * exp(∫₀ᵗ V u).

This module does NOT prove that estimate. WHAT THIS MODULE DOES NOT PROVE:
any quantitative envelope for `V u` of the constructed profile. The repo's
blowup inputs are purely qualitative (`SpeedUnboundedAtOne`; the
`Tendsto`-at-`1` hypothesis of the staged cascade), so producing the envelope
from the mechanism is construction work in the mild/fixed-point direction, not
a scalar argument.

WHAT THIS MODULE DOES PROVE: the scalar leaf is *implied* by each of two
clean envelope hypotheses, and each implication is wired through every
existing consumer (`gronwall_pair_of_rate_bound`,
`vorticity_integral_divergence_of_rate_bound`,
`lintegral_vorticity_integral_divergence_of_rate_bound`). This is the exact
surviving-proposition map for the next lane:

* `vorticityRateBound_of_sandwich_for`: a two-sided power-law envelope
  `c₁ (1-t)^(-α) ≤ V u t ≤ c₂ (1-t)^(-α)` on some `[t₀,1)` with exponent
  `α > 1` forces the leaf.
* `vorticityRateBound_of_monotoneLag_for`: monotonicity plus a sub-exponential
  lag doubling `V u t ≤ A (1 + V u (λt))^q` with `0 < λ < 1`, `q : ℕ` forces
  the leaf.

Three warnings, each checked this turn:

1. **The leaf is not generically true.** Continuous nonnegative profiles can
   violate `V ≤ C₂ e^{∫V}`: fast jumps off a slowly accumulating envelope
   outrun any fixed multiple of `e^{∫V}`. An upper envelope ALONE never
   suffices, because `∫₀ᵗ V` only sees the area accumulated before `t`
   (jump-then-envelope counterexamples). Hence both hypotheses below are
   two-sided, or carry monotonicity.
2. **Sharp constants matter.** The ODE majorization route `V' ≤ C V²` yields
   `V ≤ V₀ e^{C ∫V}`, which for `C ≠ 1` does NOT imply the leaf: `e^{C∫V}` is
   a power of `e^{∫V}`, not a constant multiple of it. Any route through a
   differential inequality must land with `C ≤ 1` against the def's integral,
   or pass through one of the two bridges below.
3. **The exponent threshold `α > 1` is exact.** For `α ≤ 1` the sandwich can
   fail for small `c₁`; the proof consumes `α > 1` through the convergent
   envelope antiderivative `(1-t)^{1-α}/(α-1)`, and there is no slack.
-/

namespace Navier.Analysis.BKMProfileRateBound

private abbrev ESpace := Navier.Construction.ProblemStatement.Space
private abbrev EVelocityField := Navier.Construction.ProblemStatement.VelocityField

/-! ## 1. Elementary domination of powers by the exponential -/

/-- `y^n ≤ n^n · e^y` on `[0,∞)`, via `y/n ≤ e^(y/n)` — no series, no
asymptotics. -/
theorem pow_le_C_exp (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, 0 ≤ y → y ^ n ≤ C * Real.exp y := by
  cases n with
  | zero => exact ⟨1, by norm_num, fun y hy => by simpa using Real.one_le_exp hy⟩
  | succ m =>
    refine ⟨((m + 1 : ℕ) : ℝ) ^ (m + 1), ?_, ?_⟩
    · positivity
    · intro y hy
      have hd : ((m + 1 : ℕ) : ℝ) ≠ 0 := by norm_cast
      have hle : y / ((m + 1 : ℕ) : ℝ) ≤ Real.exp (y / ((m + 1 : ℕ) : ℝ)) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      calc y ^ (m + 1)
          = (((m + 1 : ℕ) : ℝ) * (y / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) := by
              field_simp [hd]
        _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) * (y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) :=
            mul_pow _ _ _
        _ ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) * Real.exp (y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hle (m + 1)) (by positivity)
        _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) * Real.exp y := by
            rw [← Real.exp_nat_mul]; field_simp [hd]

/-- `y^q ≤ C e^y` on `[0,∞)` for any real exponent `q > 0`: reduce to the
integral exponent via `rpow` monotonicity. -/
theorem rpow_le_C_exp {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, 0 ≤ y → y ^ q ≤ C * Real.exp y := by
  obtain ⟨Cn, _, hCn⟩ := pow_le_C_exp (max (Nat.ceil q) 1)
  have hC : (1 : ℝ) ≤ max Cn 1 := le_max_right _ _
  have hC0 : 0 < max Cn 1 := lt_of_lt_of_le zero_lt_one hC
  refine ⟨max Cn 1, hC0, fun y hy => ?_⟩
  by_cases hy1 : y ≤ 1
  · have : y ^ q ≤ (1 : ℝ) ^ q := Real.rpow_le_rpow hy hy1 (le_of_lt hq)
    rw [Real.one_rpow] at this
    calc y ^ q ≤ 1 := this
      _ ≤ max Cn 1 := hC
      _ ≤ max Cn 1 * 1 := le_of_eq ((mul_one _).symm)
      _ ≤ max Cn 1 * Real.exp y :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp hy) (le_of_lt hC0)
  · push Not at hy1
    have hn : q ≤ ((max (Nat.ceil q) 1 : ℕ) : ℝ) :=
      (Nat.le_ceil q).trans (Nat.cast_le.mpr (Nat.le_max_left _ _))
    calc y ^ q ≤ y ^ ((max (Nat.ceil q) 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hy1) hn
      _ = y ^ (max (Nat.ceil q) 1 : ℕ) := by rw [Real.rpow_natCast]
      _ ≤ Cn * Real.exp y := hCn y (by linarith)
      _ ≤ max Cn 1 * Real.exp y :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- `(1 + y)^q ≤ C e^y` on `[0,∞)` for real exponent `q > 0`. -/
theorem one_add_rpow_le_C_exp {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, 0 ≤ y → (1 + y) ^ q ≤ C * Real.exp y := by
  obtain ⟨Cy, _, hCy⟩ := rpow_le_C_exp hq
  set Cm : ℝ := max (2 ^ q) (2 ^ q * Cy) with hCmdef
  have hCm : 0 < Cm := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) q) (le_max_left _ _)
  refine ⟨Cm, hCm, fun y hy => ?_⟩
  by_cases hy1 : y ≤ 1
  · have : (1 + y) ^ q ≤ (2 : ℝ) ^ q :=
      Real.rpow_le_rpow (by linarith) (by linarith) (le_of_lt hq)
    calc (1 + y) ^ q ≤ 2 ^ q := this
      _ ≤ Cm := le_max_left _ _
      _ ≤ Cm * 1 := le_of_eq ((mul_one _).symm)
      _ ≤ Cm * Real.exp y := mul_le_mul_of_nonneg_left (Real.one_le_exp hy) (le_of_lt hCm)
  · push Not at hy1
    have h2y : (1 + y) ^ q ≤ (2 * y) ^ q :=
      Real.rpow_le_rpow (by linarith) (by linarith) (le_of_lt hq)
    have hmul : (2 * y) ^ q = 2 ^ q * y ^ q :=
      Real.mul_rpow (by norm_num) (by linarith)
    calc (1 + y) ^ q ≤ (2 * y) ^ q := h2y
      _ = 2 ^ q * y ^ q := hmul
      _ ≤ 2 ^ q * (Cy * Real.exp y) :=
        mul_le_mul_of_nonneg_left (hCy y (by linarith))
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)
      _ = 2 ^ q * Cy * Real.exp y := by ring
      _ ≤ Cm * Real.exp y :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- `(1 + c₀ y)^q ≤ C e^y` on `[0,∞)` for `c₀ > 0` and integral exponent `q`. -/
theorem lag_pow_le_exp (q : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, 0 ≤ y → (1 + c₀ * y) ^ q ≤ C * Real.exp y := by
  obtain ⟨Cn, _, hCn⟩ := pow_le_C_exp q
  set C₁ : ℝ := max 1 c₀
  refine ⟨C₁ ^ q * Cn * Real.exp 1, by positivity, fun y hy => ?_⟩
  have hlin : 1 + c₀ * y ≤ C₁ * (1 + y) := by
    have h1 : (1 : ℝ) ≤ C₁ := le_max_left _ _
    have h2 : c₀ * y ≤ C₁ * y := mul_le_mul_of_nonneg_right (le_max_right _ _) hy
    linarith
  calc (1 + c₀ * y) ^ q ≤ (C₁ * (1 + y)) ^ q :=
        pow_le_pow_left₀ (by positivity) hlin q
      _ = C₁ ^ q * (1 + y) ^ q := mul_pow _ _ _
      _ ≤ C₁ ^ q * (Cn * Real.exp (1 + y)) :=
        mul_le_mul_of_nonneg_left (hCn (1 + y) (by linarith)) (by positivity)
      _ = C₁ ^ q * (Cn * (Real.exp 1 * Real.exp y)) := by rw [Real.exp_add]
      _ = C₁ ^ q * Cn * Real.exp 1 * Real.exp y := by ring

/-! ## 2. Bridge 1: the two-sided power-law sandwich -/

/-- **Sandwich bridge.** If the peak-vorticity profile is two-sided
power-law enveloped, `c₁ (1-t)^(-α) ≤ V u t ≤ c₂ (1-t)^(-α)` on `[t₀,1)`
with `α > 1`, then the scalar residual `VorticityRateBound u` holds. The
lower envelope forces `∫₀ᵗ V` to dominate `(1-t)^{1-α}/(α-1)`, and the upper
envelope is the `(α/(α-1))`-power of that same quantity, absorbed by the
exponential. The two-sided form is essential: see warning 1 in the module
header. -/
theorem vorticityRateBound_of_sandwich {u : EVelocityField}
    (hcont : ContinuousOn (V u) (Ico (0 : ℝ) 1))
    (hnn : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ V u t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-α) ≤ V u t)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-α)) :
    VorticityRateBound u := by
  classical
  set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, V u s with hFdef
  set q : ℝ := α / (α - 1) with hqdef
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hqpos : 0 < q := div_pos (by linarith) hα1
  have hqexp : (1 - α) * q = -α := by
    rw [hqdef]; field_simp [hα1.ne']; ring
  have hFnonneg : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ F t := by
    intro t ht
    rw [hFdef]
    exact intervalIntegral.integral_nonneg ht.1
      (fun x hx => hnn x ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩)
  have hintV : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < 1 → b < 1 →
      IntervalIntegrable (V u) volume a b := by
    intro a b ha0 hb0 ha1 hb1
    have hcu : ContinuousOn (V u) (uIcc a b) := by
      refine hcont.mono ?_
      rintro x hx
      rcases le_total a b with hab | hba
      · rw [Set.uIcc_of_le hab] at hx
        exact ⟨le_trans ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
      · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at hx
        exact ⟨le_trans hb0 hx.1, lt_of_le_of_lt hx.2 ha1⟩
    exact hcu.intervalIntegrable
  -- antiderivative of the envelope: g' x = (1 - x)^(-α) on x < 1
  set g : ℝ → ℝ := fun t => (1 / (α - 1)) * (1 - t) ^ (1 - α) with hgdef
  have hgp : ∀ x ∈ Iio (1 : ℝ), HasDerivAt g ((1 - x) ^ (-α)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).congr_deriv
        (by ring)
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ (1 - α))
        (-1 * (1 - α) * (1 - x) ^ (1 - α - 1)) x :=
      h1.rpow_const (Or.inl (by intro h; have : x < 1 := hx; linarith))
    have h4 : HasDerivAt g
        ((1 / (α - 1)) * (-1 * (1 - α) * (1 - x) ^ (1 - α - 1))) x := by
      convert h2.const_mul (1 / (α - 1)) using 1
    refine h4.congr_deriv ?_
    have he1 : (1 : ℝ) - α - 1 = -α := by ring
    rw [he1]
    field_simp [hα1.ne']
    ring
  have hintg : ∀ t ∈ Ico t₀ (1 : ℝ),
      IntervalIntegrable (fun s : ℝ => (1 - s) ^ (-α)) volume t₀ t := by
    intro t ht
    refine ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((continuousOn_const.sub continuousOn_id).rpow continuousOn_const
        (fun x hx => Or.inl (by
          intro h
          have hb : (1 : ℝ) - x = 0 := by simpa using h
          linarith [hb, hx.2, ht.2])))
  have hsub : ∀ t ∈ Ico t₀ (1 : ℝ),
      ∫ s in t₀..t, (1 - s) ^ (-α) = g t - g t₀ := by
    intro t ht
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) (hintg t ht)
    exact hgp x (lt_of_le_of_lt hx.2 (max_lt ht₀.2 ht.2))
  have hlow : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (g t - g t₀) ≤ F t := by
    intro t ht
    have hI : IntervalIntegrable (fun s : ℝ => c₁ * (1 - s) ^ (-α)) volume t₀ t :=
      (hintg t ht).const_mul c₁
    have hle : ∫ s in t₀..t, c₁ * (1 - s) ^ (-α) ≤ ∫ s in t₀..t, V u s :=
      intervalIntegral.integral_mono_on_of_le_Ioo
        (μ := volume) (hab := ht.1) (hf := hI)
        (hg := hintV t₀ t ht₀.1 (ht₀.1.trans ht.1) ht₀.2 ht.2)
        (h := fun s hs => hlen s ⟨le_of_lt hs.1, lt_trans hs.2 ht.2⟩)
    have hsplit : ∫ s in t₀..t, V u s = F t - ∫ s in (0 : ℝ)..t₀, V u s := by
      rw [hFdef]
      simpa [hFdef] using (intervalIntegral.integral_interval_sub_left
        (μ := volume)
        (hab := hintV 0 t (le_refl 0) (ht₀.1.trans ht.1) zero_lt_one ht.2)
        (hac := hintV 0 t₀ (le_refl 0) ht₀.1 zero_lt_one ht₀.2)).symm
    calc c₁ * (g t - g t₀) = c₁ * ∫ s in t₀..t, (1 - s) ^ (-α) := by rw [hsub t ht]
      _ = ∫ s in t₀..t, c₁ * (1 - s) ^ (-α) :=
        (intervalIntegral.integral_const_mul c₁ (fun s => (1 - s) ^ (-α))).symm
      _ ≤ ∫ s in t₀..t, V u s := hle
      _ ≤ F t := by
        rw [hsplit]
        exact sub_le_self _ (hFnonneg t₀ ht₀)
  -- envelope identity: (1-t)^(-α) = ((α-1) * g t)^q
  have hident : ∀ t ∈ Ico t₀ (1 : ℝ), (1 - t) ^ (-α) = ((α - 1) * g t) ^ q := by
    intro t ht
    have hgt : (α - 1) * g t = (1 - t) ^ (1 - α) := by
      rw [hgdef]; field_simp [hα1.ne']
    rw [hgt, ← Real.rpow_mul (show (0 : ℝ) ≤ 1 - t by linarith [ht.2]) (1 - α) q, hqexp]
  obtain ⟨Cexp, _, hCexp⟩ := one_add_rpow_le_C_exp hqpos
  have hg0 : 0 ≤ g t₀ := by
    refine mul_nonneg (div_nonneg zero_le_one (le_of_lt hα1))
      (Real.rpow_nonneg (by linarith [ht₀.2] : (0 : ℝ) ≤ 1 - t₀) (1 - α))
  have hc1n : (0 : ℝ) ≤ 1 / c₁ := by positivity
  have hgsum : 0 ≤ g t₀ + 1 / c₁ := by linarith
  have htail : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤
      (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp) * Real.exp (F t) := by
    intro t ht
    have hF : 0 ≤ F t := hFnonneg t ⟨ht₀.1.trans ht.1, ht.2⟩
    have hgb : 0 ≤ g t :=
      mul_nonneg (div_nonneg zero_le_one (le_of_lt hα1))
        (Real.rpow_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) (1 - α))
    have hgl : g t ≤ g t₀ + (1 / c₁) * F t := by
      have h := hlow t ht
      have hdiv : g t - g t₀ ≤ F t / c₁ :=
        (le_div_iff₀ hc₁).mpr (by rw [mul_comm]; exact h)
      have hfe : F t / c₁ = (1 / c₁) * F t := by ring
      linarith
    have h4 : (1 / c₁) * F t ≤ (g t₀ + 1 / c₁) * F t :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hg0) hF
    have hgl2 : g t ≤ (g t₀ + 1 / c₁) + (g t₀ + 1 / c₁) * F t := by
      linarith [hgl, h4, hc1n]
    have hT : (g t₀ + 1 / c₁) * (1 + F t)
        = (g t₀ + 1 / c₁) + (g t₀ + 1 / c₁) * F t := by ring
    have hgl6 : g t ≤ (g t₀ + 1 / c₁) * (1 + F t) := by rw [hT]; exact hgl2
    have hpow : g t ^ q ≤ (g t₀ + 1 / c₁) ^ q * (1 + F t) ^ q := by
      calc g t ^ q ≤ ((g t₀ + 1 / c₁) * (1 + F t)) ^ q :=
          Real.rpow_le_rpow hgb hgl6 (le_of_lt hqpos)
        _ = (g t₀ + 1 / c₁) ^ q * (1 + F t) ^ q :=
          Real.mul_rpow hgsum (by linarith [hF])
    have he : (1 + F t) ^ q ≤ Cexp * Real.exp (F t) := hCexp (F t) hF
    have hsplitq : (α - 1) ^ q * (g t₀ + 1 / c₁) ^ q
        = ((α - 1) * (g t₀ + 1 / c₁)) ^ q :=
      (Real.mul_rpow (by linarith) hgsum).symm
    calc V u t ≤ c₂ * (1 - t) ^ (-α) := hup t ht
      _ = c₂ * ((α - 1) * g t) ^ q := by rw [hident t ht]
      _ = c₂ * ((α - 1) ^ q * g t ^ q) := by
        rw [Real.mul_rpow (by linarith) hgb]
      _ ≤ c₂ * ((α - 1) ^ q * ((g t₀ + 1 / c₁) ^ q * (1 + F t) ^ q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow
            (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ α - 1) q)) hc₂
      _ = c₂ * (((α - 1) ^ q * (g t₀ + 1 / c₁) ^ q) * (1 + F t) ^ q) := by
        rw [mul_assoc]
      _ = (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q) * (1 + F t) ^ q := by
        rw [hsplitq, mul_assoc]
      _ ≤ (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q) * (Cexp * Real.exp (F t)) :=
        mul_le_mul_of_nonneg_left he
          (mul_nonneg hc₂ (Real.rpow_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ α - 1 from by linarith) hgsum) q))
      _ = (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp) * Real.exp (F t) := by ring
  obtain ⟨a, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    ⟨0, le_refl 0, ht₀.1⟩
    (hcont.mono (by rintro x ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_lt h2 ht₀.2⟩))
  have hC2 : 0 ≤ max (max (V u a) 0) (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp) :=
    le_trans (le_max_right (V u a) 0) (le_max_left _ _)
  refine ⟨max (max (V u a) 0) (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp),
    hC2, fun t ht => ?_⟩
  by_cases hle' : t ≤ t₀
  · have := hmax ⟨ht.1, hle'⟩
    calc V u t ≤ V u a := this
      _ ≤ max (V u a) 0 := le_max_left _ _
      _ ≤ max (max (V u a) 0) (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp) :=
        le_max_left _ _
      _ ≤ _ * 1 := le_of_eq ((mul_one _).symm)
      _ ≤ _ * Real.exp (F t) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (hFnonneg t ht)) hC2
  · have ht2 : t ∈ Ico t₀ (1 : ℝ) := ⟨le_of_lt (lt_of_not_ge hle'), ht.2⟩
    calc V u t ≤ (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp) * Real.exp (F t) :=
        htail t ht2
      _ ≤ max (max (V u a) 0) (c₂ * ((α - 1) * (g t₀ + 1 / c₁)) ^ q * Cexp)
          * Real.exp (F t) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ## 3. Bridge 2: monotonicity plus sub-exponential lag doubling -/

/-- **Monotone-lag bridge.** If the peak-vorticity profile is monotone on
`[0,1)` and satisfies a lag-doubling inequality `V u t ≤ A (1 + V u (λt))^q`
with `0 < λ < 1` and integral exponent `q`, then `VorticityRateBound u`
holds. The monotonicity turns the lag window `[λt, t]` into a pointwise
lower bound on `∫₀ᵗ V`, and `(1 + c·y)^q ≤ C e^y` absorbs the power. This is
the shape matched by the staged cascade: per-stage gains of the form
`h·j/10` over geometrically spaced time windows. -/
theorem vorticityRateBound_of_monotoneLag {u : EVelocityField}
    (hcont : ContinuousOn (V u) (Ico (0 : ℝ) 1))
    (hnn : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ V u t)
    (hmono : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, x ≤ y → V u x ≤ V u y)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {A : ℝ} (hA : 0 ≤ A) (q : ℕ)
    (hlag : ∀ t ∈ Ico (0 : ℝ) 1, V u t ≤ A * (1 + V u (lam * t)) ^ q) :
    VorticityRateBound u := by
  classical
  set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, V u s with hFdef
  have hFnonneg : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ F t := by
    intro t ht
    rw [hFdef]
    exact intervalIntegral.integral_nonneg ht.1
      (fun x hx => hnn x ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩)
  have hintV : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < 1 → b < 1 →
      IntervalIntegrable (V u) volume a b := by
    intro a b ha0 hb0 ha1 hb1
    have hcu : ContinuousOn (V u) (uIcc a b) := by
      refine hcont.mono ?_
      rintro x hx
      rcases le_total a b with hab | hba
      · rw [Set.uIcc_of_le hab] at hx
        exact ⟨le_trans ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
      · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at hx
        exact ⟨le_trans hb0 hx.1, lt_of_le_of_lt hx.2 ha1⟩
    exact hcu.intervalIntegrable
  set δ : ℝ := (1 - lam) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hc₀ : 0 < 2 / (1 - lam) := div_pos (by norm_num) (by linarith)
  obtain ⟨K, _, hKlag⟩ := lag_pow_le_exp q hc₀
  have harea : ∀ t ∈ Ico (0 : ℝ) 1, (1 / 2 : ℝ) ≤ t →
      ∫ s in (lam * t)..t, V u s ≤ F t := by
    intro t ht hthalf
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : lam * t < t := by simpa using mul_lt_mul_of_pos_right hlam1 ht0
    have hlamt : lam * t ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hlam.le ht.1, lt_trans hlt ht.2⟩
    have hpos : 0 ≤ ∫ s in (0 : ℝ)..lam * t, V u s := hFnonneg (lam * t) hlamt
    have heq : ∫ s in (lam * t)..t, V u s = F t - ∫ s in (0 : ℝ)..lam * t, V u s := by
      rw [hFdef]
      simpa [hFdef] using (intervalIntegral.integral_interval_sub_left
        (μ := volume)
        (hab := hintV 0 t (le_refl 0) ht.1 zero_lt_one ht.2)
        (hac := hintV 0 (lam * t) (le_refl 0) (mul_nonneg hlam.le ht.1)
          zero_lt_one hlamt.2)).symm
    rw [heq]; linarith
  have hconst : ∀ t ∈ Ico (0 : ℝ) 1, (1 / 2 : ℝ) ≤ t →
      δ * V u (lam * t) ≤ ∫ s in (lam * t)..t, V u s := by
    intro t ht hthalf
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : lam * t < t := by simpa using mul_lt_mul_of_pos_right hlam1 ht0
    have hlamt : lam * t ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hlam.le ht.1, lt_trans hlt ht.2⟩
    have hsl : 0 ≤ V u (lam * t) := hnn (lam * t) hlamt
    have h1 : δ ≤ t - lam * t := by
      rw [hδdef]
      have hnon : (0 : ℝ) ≤ 1 - lam := by linarith
      have : t - lam * t = t * (1 - lam) := by ring
      nlinarith
    have h2 : δ * V u (lam * t) ≤ (t - lam * t) * V u (lam * t) :=
      mul_le_mul_of_nonneg_right h1 hsl
    have h3 : (t - lam * t) * V u (lam * t) = ∫ s in (lam * t)..t, V u (lam * t) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have h4 : ∫ s in (lam * t)..t, V u (lam * t) ≤ ∫ s in (lam * t)..t, V u s :=
      intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
        (hab := le_of_lt hlt)
        (hf := continuousOn_const.intervalIntegrable)
        (hg := hintV (lam * t) t (mul_nonneg hlam.le ht.1) ht.1
          (lt_trans hlt ht.2) ht.2)
        (h := fun s hs => hmono (lam * t) hlamt s
          ⟨le_of_lt (lt_of_le_of_lt (mul_nonneg hlam.le ht.1) hs.1),
            lt_trans hs.2 ht.2⟩
          (le_of_lt hs.1))
    calc δ * V u (lam * t) ≤ (t - lam * t) * V u (lam * t) := h2
      _ = ∫ s in (lam * t)..t, V u (lam * t) := h3
      _ ≤ ∫ s in (lam * t)..t, V u s := h4
  obtain ⟨a, _, hmax⟩ :=
    IsCompact.exists_isMaxOn (s := Icc (0 : ℝ) (1 / 2)) isCompact_Icc
      ⟨0, by norm_num, by norm_num⟩
      (hcont.mono (by rintro x ⟨h1, h2⟩; exact ⟨h1, by linarith⟩))
  have hC2 : 0 ≤ max (max (V u a) 0) (A * K) :=
    le_trans (le_max_right (V u a) 0) (le_max_left _ _)
  refine ⟨max (max (V u a) 0) (A * K), hC2, fun t ht => ?_⟩
  by_cases hle' : t ≤ (1 / 2 : ℝ)
  · have := hmax ⟨ht.1, hle'⟩
    calc V u t ≤ V u a := this
      _ ≤ max (V u a) 0 := le_max_left _ _
      _ ≤ max (max (V u a) 0) (A * K) := le_max_left _ _
      _ ≤ _ * 1 := le_of_eq ((mul_one _).symm)
      _ ≤ _ * Real.exp (F t) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (hFnonneg t ht)) hC2
  · have hthalf : (1 / 2 : ℝ) ≤ t := le_of_not_ge hle'
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : lam * t < t := by simpa using mul_lt_mul_of_pos_right hlam1 ht0
    have hlamt : lam * t ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hlam.le ht.1, lt_trans hlt ht.2⟩
    have hbnd : V u (lam * t) ≤ (2 / (1 - lam)) * F t := by
      have h := le_trans (hconst t ht hthalf) (harea t ht hthalf)
      have hdiv : V u (lam * t) ≤ F t / δ :=
        (le_div_iff₀ hδ).mpr (by rw [mul_comm]; exact h)
      have hfe : F t / δ = (2 / (1 - lam)) * F t := by
        rw [hδdef]; field_simp
      linarith
    calc V u t ≤ A * (1 + V u (lam * t)) ^ q := hlag t ht
      _ ≤ A * (1 + (2 / (1 - lam)) * F t) ^ q :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [hnn (lam * t) hlamt])
            (by linarith [hbnd]) q) hA
      _ ≤ A * (K * Real.exp (F t)) :=
        mul_le_mul_of_nonneg_left (hKlag (F t) (hFnonneg t ht)) hA
      _ = (A * K) * Real.exp (F t) := by ring
      _ ≤ max (max (V u a) 0) (A * K) * Real.exp (F t) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ## 4. Field wrappers and wiring through the existing consumers -/

/-- The sandwich envelope, stated for the selected profile's peak-vorticity
function `V u`, yields the named scalar residual. -/
theorem vorticityRateBound_of_sandwich_for {u p f : _} (h : Properties u p f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-α) ≤ V u t)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-α)) :
    VorticityRateBound u := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  exact vorticityRateBound_of_sandwich
    (V_continuousOn h.velocity_smooth hK hsupp)
    (fun t ht => V_nonneg h.velocity_smooth hK hsupp ht) ht₀ hα hc₁ hc₂ hlen hup

/-- The monotone-lag envelope, stated for `V u`, yields the named scalar
residual. -/
theorem vorticityRateBound_of_monotoneLag_for {u p f : _} (h : Properties u p f)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {A : ℝ} (hA : 0 ≤ A) (q : ℕ)
    (hmono : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, x ≤ y → V u x ≤ V u y)
    (hlag : ∀ t ∈ Ico (0 : ℝ) 1, V u t ≤ A * (1 + V u (lam * t)) ^ q) :
    VorticityRateBound u := by
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  exact vorticityRateBound_of_monotoneLag
    (V_continuousOn h.velocity_smooth hK hsupp)
    (fun t ht => V_nonneg h.velocity_smooth hK hsupp ht) hmono hlam hlam1 hA q hlag

theorem gronwall_pair_of_sandwich_for {u p f : _} (h : Properties u p f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-α) ≤ V u t)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-α)) :
    GronwallPair u :=
  gronwall_pair_of_rate_bound h
    (vorticityRateBound_of_sandwich_for h ht₀ hα hc₁ hc₂ hlen hup)

theorem vorticity_integral_divergence_of_sandwich_for {u p f : _}
    (h : Properties u p f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-α) ≤ V u t)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-α)) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B :=
  vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_sandwich_for h ht₀ hα hc₁ hc₂ hlen hup)

theorem lintegral_vorticity_integral_divergence_of_sandwich_for {u p f : _}
    (h : Properties u p f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) {α : ℝ} (hα : 1 < α)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-α) ≤ V u t)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-α)) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ :=
  lintegral_vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_sandwich_for h ht₀ hα hc₁ hc₂ hlen hup)

theorem gronwall_pair_of_monotoneLag_for {u p f : _} (h : Properties u p f)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {A : ℝ} (hA : 0 ≤ A) (q : ℕ)
    (hmono : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, x ≤ y → V u x ≤ V u y)
    (hlag : ∀ t ∈ Ico (0 : ℝ) 1, V u t ≤ A * (1 + V u (lam * t)) ^ q) :
    GronwallPair u :=
  gronwall_pair_of_rate_bound h
    (vorticityRateBound_of_monotoneLag_for h hlam hlam1 hA q hmono hlag)

theorem vorticity_integral_divergence_of_monotoneLag_for {u p f : _}
    (h : Properties u p f)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {A : ℝ} (hA : 0 ≤ A) (q : ℕ)
    (hmono : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, x ≤ y → V u x ≤ V u y)
    (hlag : ∀ t ∈ Ico (0 : ℝ) 1, V u t ≤ A * (1 + V u (lam * t)) ^ q) :
    ¬ ∃ B : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, V u s ≤ B :=
  vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_monotoneLag_for h hlam hlam1 hA q hmono hlag)

theorem lintegral_vorticity_integral_divergence_of_monotoneLag_for {u p f : _}
    (h : Properties u p f)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {A : ℝ} (hA : 0 ≤ A) (q : ℕ)
    (hmono : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, x ≤ y → V u x ≤ V u y)
    (hlag : ∀ t ∈ Ico (0 : ℝ) 1, V u t ≤ A * (1 + V u (lam * t)) ^ q) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (V u t) = ⊤ :=
  lintegral_vorticity_integral_divergence_of_rate_bound h
    (vorticityRateBound_of_monotoneLag_for h hlam hlam1 hA q hmono hlag)

end Navier.Analysis.BKMProfileRateBound

#check @Navier.Analysis.BKMProfileRateBound.pow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.pow_le_C_exp
#check @Navier.Analysis.BKMProfileRateBound.rpow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.rpow_le_C_exp
#check @Navier.Analysis.BKMProfileRateBound.one_add_rpow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.one_add_rpow_le_C_exp
#check @Navier.Analysis.BKMProfileRateBound.lag_pow_le_exp
#print axioms Navier.Analysis.BKMProfileRateBound.lag_pow_le_exp
#check @Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich
#check @Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag
#check @Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_sandwich_for
#check @Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_sandwich_for
#check @Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_monotoneLag_for
#print axioms Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_monotoneLag_for
