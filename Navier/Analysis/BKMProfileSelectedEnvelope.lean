/-
Original work, lane L6b6, 2026-09-14.

# The polynomial-upper / axis-lower envelope bridge (third bridge)

`BKMProfileRateBound.lean` carries two bridges into the scalar leaf
`VorticityRateBound u` (`BKMProfileGronwallPair.lean:109`): the two-sided
sandwich (which requires the SAME exponent `α > 1` on both envelopes — the
consuming note in `BKMProfileEnvelope.lean:94-134` lists the transports that
would instantiate it for the selected field `u_sel` of
`ActualCandidateAssembly`/`R3CompactCandidate`, and lane L6b5's diagnosis was
that the stage-cascade ledger supplies an upper polynomial rate `αU ≈ 4-6`
while the axis lower rate is `1 + h < 3/2`, so the sandwich exponents do not
match), and the monotone-lag bridge.

This module lands the THIRD bridge, designed to make the exponent-matching
obligation disappear entirely: the upper envelope may have ANY real power-law
rate `β` (no `β > 1`, no relation to the lower rate), while the axis lower
envelope keeps the integrable-growth requirement `αL > 1`. The leaf then
follows because `exp(∫₀ᵗ V)` dominates `e^{λ·(1-t)^{-(αL-1)}}`, and every
polynomial `(1-t)^{-β}` is dominated by that exponential (the `rpow`-vs-`exp`
absorption via the public `BKMProfileRateBound.rpow_le_C_exp`, applied at the
rescaled variable `λ·(1-t)^{-(αL-1)}` whose scale `λ = c₁/(αL-1)` is supplied
by the axis lower bound's own antiderivative).

Concrete consumption (next slice, hypothesis names from the lane plan):
* the upper hypothesis `hup` is instantiated at `β := αU` by the summation
  transport T1 over `DiagonalJetBounds.exists_potential_tail_order` plus the
  stage-0 bound and the curl/cut assembly transports (transports 1-4 of
  `BKMProfileEnvelope.lean:94-134`; with this bridge their exponents no
  longer need to match anything);
* the lower hypothesis `haxis` is the axis eventual-equality conversion of
  lane L6b4's landed `Navier/Construction/BaseVorticityAxis.lean`
  `FinalSlowBase.axis_vorticity_origin` (cited, not reproduced here: that
  file is not in this checkout) at exponent `A h + 1/2 = 1 + h > 1`
  (`CoordinateAlgebra.lean:25`), consumed as a named hypothesis pending the
  germ-neighborhood upgrade through `GermCandidateAssembly.
  origin_eventually_base` (`.lean:116`) and
  `TimeLocalization.activatedVelocity_eventuallyEq_late` (`.lean:91`);
* `hbdd` is a one-liner from
  `BKMVorticityIntegralDivergence.V_continuousOn` +
  `IsCompact.exists_forall_le` on `[0, t₀]`.

This module makes NO declaration unconditional; it is an implication whose
hypotheses are pointwise envelope statements about `V u`/the axis vorticity,
strictly local and none of them the conclusion.
-/
import Navier.Analysis.BKMProfileEnvelope

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators ContDiff
open Navier Navier.Analysis.Vorticity Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BKMForcedBreakdownNecessity
open Navier.Analysis.BKMProfileGronwallPair
open Navier.Analysis.BKMProfileRateBound
open Navier.Analysis.BKMVorticityIntegralDivergence
open Navier.Construction.ProblemStatement
open Navier.Construction.R3CompactCandidate

namespace Navier.Analysis.BKMProfileSelectedEnvelope

/-! ## The bridge. -/

/-- **Polynomial-upper / axis-lower bridge.** Let `u` be a competitor with the
`R3CompactCandidate.Properties` package (supplying the spatial compact support
and smoothness that make the peak-vorticity profile `V u` continuous and
nonnegative on `[0,1)`). If on some `[t₀,1)` the profile has a polynomial
UPPER envelope `V u t ≤ c₂ (1-t)^(-β)` for an arbitrary real rate `β`, the
axis vorticity has an integrable-growth LOWER envelope
`c₁ (1-t)^(-αL) ≤ officialEuclideanNorm (vorticity (uncurry u) t 0)` with
`αL > 1`, and `V u` is bounded on `[0, t₀]`, then `VorticityRateBound u`
holds. Unlike `vorticityRateBound_of_sandwich` the two exponents are
independent: `β` may be any real number, so no ledger matching is required.
-/
theorem vorticityRateBound_of_polyUpper_axisLower
    {u p f : _} (h : Properties u p f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    {β c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hup : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤ c₂ * (1 - t) ^ (-β))
    {αL c₁ : ℝ} (hc₁ : 0 < c₁) (hαL : (1 : ℝ) < αL)
    (haxis : ∀ t ∈ Ico t₀ (1 : ℝ),
      c₁ * (1 - t) ^ (-αL) ≤
        officialEuclideanNorm (vorticity (uncurry u) t (0 : Navier.Space)))
    (hbdd : ∃ C₃, ∀ t ∈ Ico (0 : ℝ) t₀, V u t ≤ C₃) :
    VorticityRateBound u := by
  classical
  obtain ⟨K, hK, hsupp⟩ := h.velocity_support
  have hcont : ContinuousOn (V u) (Ico (0 : ℝ) 1) :=
    V_continuousOn h.velocity_smooth hK hsupp
  have hnn : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ V u t :=
    fun t ht => V_nonneg h.velocity_smooth hK hsupp ht
  have hlen : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (1 - t) ^ (-αL) ≤ V u t := by
    intro t ht
    exact (haxis t ht).trans
      (vort_le_V h.velocity_smooth hK hsupp ⟨ht₀.1.trans ht.1, ht.2⟩
        (0 : Navier.Space))
  -- boundedness on `[0, t₀]`, normalized to a nonnegative constant
  obtain ⟨C₃₀, hC₃₀n, hC₃₀⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico (0 : ℝ) t₀, V u t ≤ C := by
    obtain ⟨C₃, hC₃⟩ := hbdd
    rcases eq_or_lt_of_le ht₀.1 with rfl | ht₀0
    · exact ⟨0, le_refl 0, fun t ht => absurd ht.2 (not_lt_of_ge ht.1)⟩
    · exact ⟨max 0 C₃, le_max_left 0 C₃,
        fun t ht => (hC₃ t ht).trans (le_max_right 0 C₃)⟩
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
  -- antiderivative of the axis lower envelope on `t < 1`
  have hpE : (0 : ℝ) < αL - 1 := by linarith
  set G : ℝ → ℝ := fun t => (1 / (αL - 1)) * (1 - t) ^ (1 - αL) with hGdef
  have hGp : ∀ x ∈ Iio (1 : ℝ), HasDerivAt G ((1 - x) ^ (-αL)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).congr_deriv
        (by ring)
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ (1 - αL))
        (-1 * (1 - αL) * (1 - x) ^ (1 - αL - 1)) x :=
      h1.rpow_const (Or.inl (by intro hz; have : x < 1 := hx; linarith))
    have h4 : HasDerivAt G
        ((1 / (αL - 1)) * (-1 * (1 - αL) * (1 - x) ^ (1 - αL - 1))) x := by
      convert h2.const_mul (1 / (αL - 1)) using 1
    refine h4.congr_deriv ?_
    have he1 : (1 : ℝ) - αL - 1 = -αL := by ring
    rw [he1]
    field_simp [hpE.ne']
    ring
  have hintG : ∀ t ∈ Ico t₀ (1 : ℝ),
      IntervalIntegrable (fun s : ℝ => (1 - s) ^ (-αL)) volume t₀ t := by
    intro t ht
    refine ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((continuousOn_const.sub continuousOn_id).rpow continuousOn_const
        (fun x hx => Or.inl (by
          intro hz
          have hb : (1 : ℝ) - x = 0 := by simpa using hz
          linarith [hb, hx.2, ht.2])))
  have hsub : ∀ t ∈ Ico t₀ (1 : ℝ),
      ∫ s in t₀..t, (1 - s) ^ (-αL) = G t - G t₀ := by
    intro t ht
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
      (hintG t ht)
    exact hGp x (lt_of_le_of_lt hx.2 (max_lt ht₀.2 ht.2))
  -- the axis lower bound forces `∫₀ᵗ V ≥ c₁ (G t - G t₀)`
  have hlow : ∀ t ∈ Ico t₀ (1 : ℝ), c₁ * (G t - G t₀) ≤ F t := by
    intro t ht
    have hI : IntervalIntegrable (fun s : ℝ => c₁ * (1 - s) ^ (-αL)) volume t₀ t :=
      (hintG t ht).const_mul c₁
    have hle : ∫ s in t₀..t, c₁ * (1 - s) ^ (-αL) ≤ ∫ s in t₀..t, V u s :=
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
    calc c₁ * (G t - G t₀) = c₁ * ∫ s in t₀..t, (1 - s) ^ (-αL) := by rw [hsub t ht]
      _ = ∫ s in t₀..t, c₁ * (1 - s) ^ (-αL) :=
        (intervalIntegral.integral_const_mul c₁ (fun s => (1 - s) ^ (-αL))).symm
      _ ≤ ∫ s in t₀..t, V u s := hle
      _ ≤ F t := by
        rw [hsplit]
        exact sub_le_self _ (hFnonneg t₀ ht₀)
  -- any polynomial rate is absorbed: raise `β` to `βmax ≥ 1` and use
  -- `(1-t)^(-βmax) = ((1-t)^(-(αL-1)))^(βmax/(αL-1))` against `rpow_le_C_exp`
  set βmax : ℝ := max β 1 with hβmaxdef
  have hβle : β ≤ βmax := le_max_left β 1
  have hβmaxpos : (0 : ℝ) < βmax := lt_of_lt_of_le zero_lt_one (le_max_right β 1)
  set pE : ℝ := αL - 1 with hpEdef
  have hpE0 : (0 : ℝ) < pE := hpE
  set q : ℝ := βmax / pE with hqdef
  have hq : (0 : ℝ) < q := div_pos hβmaxpos hpE0
  set lam : ℝ := c₁ / pE with hlamdef
  have hlam : (0 : ℝ) < lam := div_pos hc₁ hpE0
  obtain ⟨Cexp, hCexp, hce⟩ := rpow_le_C_exp hq
  have htail : ∀ t ∈ Ico t₀ (1 : ℝ), V u t ≤
      (c₂ * (Cexp * (lam⁻¹) ^ q) * Real.exp (lam * ((1 - t₀) ^ (-pE)))) *
        Real.exp (F t) := by
    intro t ht
    have hx : (1 - t) ^ (-βmax) = ((lam * (1 - t) ^ (-pE)) * lam⁻¹) ^ q := by
      have key : (lam * (1 - t) ^ (-pE)) * lam⁻¹ = (1 - t) ^ (-pE) := by
        rw [mul_comm lam _, mul_inv_cancel_right₀ hlam.ne']
      have hmulq : ((-pE) * q : ℝ) = -βmax := by
        rw [hqdef]
        have h : pE * (βmax / pE) = βmax := by
          rw [mul_comm, div_mul_cancel₀ βmax hpE0.ne']
        calc (-pE) * (βmax / pE) = -(pE * (βmax / pE)) := neg_mul _ _
          _ = -βmax := congrArg Neg.neg h
      rw [key, ← hmulq]
      exact Real.rpow_mul (show (0 : ℝ) ≤ 1 - t by linarith [ht.2]) (-pE) q
    have hle2 : (1 - t) ^ (-β) ≤ (1 - t) ^ (-βmax) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith [ht.2])
        (by linarith [ht.1, ht₀.1]) (neg_le_neg hβle)
    have hy0 : 0 ≤ lam * (1 - t) ^ (-pE) :=
      mul_nonneg hlam.le (Real.rpow_nonneg (by linarith [ht.2]) (-pE))
    have hmul : ((lam * (1 - t) ^ (-pE)) * lam⁻¹) ^ q =
        (lam * (1 - t) ^ (-pE)) ^ q * (lam⁻¹) ^ q :=
      Real.mul_rpow (by positivity) (by positivity)
    -- `exp (lam * (1-t)^(-pE)) ≤ exp (lam * (1-t₀)^(-pE)) * exp (F t)`
    have hlamt : lam * (1 - t) ^ (-pE) =
        lam * (1 - t₀) ^ (-pE) + c₁ * (G t - G t₀) := by
      have hneg : (1 : ℝ) - αL = -pE := by
        rw [hpEdef]
        ring
      have hgG : G t = (1 - t) ^ (-pE) / pE ∧ G t₀ = (1 - t₀) ^ (-pE) / pE := by
        constructor
        · rw [hGdef, hneg]
          field_simp [hpE0.ne']
        · rw [hGdef, hneg]
          field_simp [hpE0.ne']
      have h1 : c₁ * (G t - G t₀)
          = c₁ * ((1 - t) ^ (-pE) / pE - (1 - t₀) ^ (-pE) / pE) := by
        rw [hgG.1, hgG.2]
      have h2 : c₁ * ((1 - t) ^ (-pE) / pE - (1 - t₀) ^ (-pE) / pE)
          = (c₁ / pE) * ((1 - t) ^ (-pE) - (1 - t₀) ^ (-pE)) := by
        field_simp [hpE0.ne']
      have h4 : c₁ * (G t - G t₀)
          = lam * ((1 - t) ^ (-pE) - (1 - t₀) ^ (-pE)) := by
        rw [h1, h2, ← hlamdef]
      rw [h4]
      ring
    have hexp2 : Real.exp (lam * (1 - t) ^ (-pE)) ≤
        Real.exp (lam * (1 - t₀) ^ (-pE)) * Real.exp (F t) := by
      have hge : c₁ * (G t - G t₀) ≤ F t := hlow t ht
      calc Real.exp (lam * (1 - t) ^ (-pE))
          = Real.exp (lam * (1 - t₀) ^ (-pE)) * Real.exp (c₁ * (G t - G t₀)) := by
            rw [hlamt, Real.exp_add]
        _ ≤ Real.exp (lam * (1 - t₀) ^ (-pE)) * Real.exp (F t) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hge)
            (Real.exp_pos _).le
    calc V u t ≤ c₂ * (1 - t) ^ (-β) := hup t ht
      _ ≤ c₂ * (1 - t) ^ (-βmax) := mul_le_mul_of_nonneg_left hle2 hc₂
      _ = c₂ * ((lam * (1 - t) ^ (-pE)) * lam⁻¹) ^ q := by rw [hx]
      _ = c₂ * ((lam * (1 - t) ^ (-pE)) ^ q * (lam⁻¹) ^ q) := by rw [hmul]
      _ ≤ c₂ * (Cexp * Real.exp (lam * (1 - t) ^ (-pE)) * (lam⁻¹) ^ q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hce _ hy0) (Real.rpow_nonneg
            (le_of_lt (inv_pos.mpr hlam)) q)) hc₂
      _ = c₂ * ((Cexp * (lam⁻¹) ^ q) * Real.exp (lam * (1 - t) ^ (-pE))) := by ring
      _ ≤ c₂ * ((Cexp * (lam⁻¹) ^ q) *
          (Real.exp (lam * (1 - t₀) ^ (-pE)) * Real.exp (F t))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp2
            (mul_nonneg hCexp.le
              (Real.rpow_nonneg (le_of_lt (inv_pos.mpr hlam)) q)))
          hc₂
      _ = (c₂ * (Cexp * (lam⁻¹) ^ q) * Real.exp (lam * ((1 - t₀) ^ (-pE)))) *
          Real.exp (F t) := by ring
  -- assemble the leaf constant
  set C₂ : ℝ := max C₃₀
    (c₂ * (Cexp * (lam⁻¹) ^ q) * Real.exp (lam * ((1 - t₀) ^ (-pE)))) with hC₂def
  have hC₂ : 0 ≤ C₂ :=
    le_trans hC₃₀n (le_max_left C₃₀ _)
  refine ⟨C₂, hC₂, fun t ht => ?_⟩
  by_cases hlt : t < t₀
  · calc V u t ≤ C₃₀ := hC₃₀ t ⟨ht.1, hlt⟩
      _ ≤ C₂ := le_max_left _ _
      _ ≤ C₂ * 1 := le_of_eq ((mul_one _).symm)
      _ ≤ C₂ * Real.exp (F t) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (hFnonneg t ht)) hC₂
  · have ht2 : t ∈ Ico t₀ (1 : ℝ) := ⟨by linarith, ht.2⟩
    calc V u t ≤
        (c₂ * (Cexp * (lam⁻¹) ^ q) * Real.exp (lam * ((1 - t₀) ^ (-pE)))) *
          Real.exp (F t) := htail t ht2
      _ ≤ C₂ * Real.exp (F t) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end Navier.Analysis.BKMProfileSelectedEnvelope

#check @Navier.Analysis.BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower
#print axioms Navier.Analysis.BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower
