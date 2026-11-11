import Mathlib
import Navier.Analysis.OsgoodUniformBound

/-!
# Osgood divergence bridge: the crown's `ENNReal` divergence hypothesis IS the
# transform divergence `OsgoodUniformBound` consumes.

`Navier/Analysis/CrownBridgeReduction.lean` states Osgood divergence as
`(∫⁻ u in Ici 1, ENNReal.ofReal ((ω u)⁻¹)) = ⊤` (its §3 leaf and its
`OsgoodEnvelopeMajorant`), while the uniform horizon-local cap
`Navier.Analysis.OsgoodUniformBound.exists_nnreal_bound_of_osgoodBarrier`
(landed at `25d4018`) consumes the form
`Tendsto (osgExt (majExt ω)) atTop atTop`.  That module's header records the
bridge as NOT certified there, and `QP1110-NAVIER-SORRY2`'s receipt §5 named
disjoint annuli plus `lintegral_iUnion` plus `tsum_eq_iSup_sum` as the workable
route because, it reported, this Mathlib revision carries no set-lintegral
continuity-from-below lemma.

Measured correction (this pin, `1f414401f690`): the continuity-from-below lemma
does exist under another name —
`MeasureTheory.setLIntegral_iUnion_of_directed`
(`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:668`,
`∫⁻ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁻ x in s i, f x ∂μ` for a countable
`Directed (· ⊆ ·)` family).  With it the bridge needs no annuli, no `tsum`, and
no `Set.indicator` shuffling: the truncation family `n ↦ Icc 1 (n+1)` is
directed, its union is EXACTLY `Ici 1` (the closed left endpoint is what removes
the null-set step the sibling's `Ioc` family forced), and the Bochner side is
transported by `MeasureTheory.integral_Icc_eq_integral_Ioc`.

* `ofReal_osgExt_majExt_eq_lintegral` — each truncation of the extended Osgood
  transform is the `Icc`-lintegral of the reciprocal extended majorant.
* `tendsto_osgExt_majExt_atTop` — the crown's divergence hypothesis forces the
  extended transform above every real.
* `exists_nnreal_bound_of_osgoodMajorant` — the uniform cap fed by that bridge,
  in the crown's own binder order (`∃ M : ℝ≥0` chosen BEFORE the unknown `y`),
  which is the order `AprioriCriticalControlQuantifiers.HorizonLocalCriticalControl`
  needs (`∃ M` sits before `∀ u p`).

This module closes the comparison side of `CrownBridgeReduction` §4.  What it
does NOT close is §4's envelope time-continuity producer, recorded in
`Navier/Analysis/OsgoodEnvelopeTransfer.lean`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal Topology MeasureTheory
open Set Filter MeasureTheory intervalIntegral
open Navier.Analysis.OsgoodUniformBound

namespace Navier.Analysis.OsgoodDivergenceBridge

/-- The extended majorant clamps its argument at `0`, so it agrees with the
majorant itself on `[1, ∞)`. -/
theorem majExt_eq_on_Ici {ω : ℝ → ℝ} (u : ℝ) (hu : u ∈ Ici (1 : ℝ)) : majExt ω u = ω u :=
  congr_arg ω (max_eq_left (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hu))

/-- **Truncation identity.**  For every `n`, the extended Osgood transform at
`n + 1`, pushed through `ENNReal.ofReal`, is the set lintegral of the
reciprocal extended majorant over `Icc 1 (n+1)`. -/
theorem ofReal_osgExt_majExt_eq_lintegral {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) (n : ℕ) :
    ENNReal.ofReal (osgExt (majExt ω) ((n : ℝ) + 1)) =
      ∫⁻ u in Icc (1 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ((majExt ω u)⁻¹) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hg : Continuous (fun u : ℝ => (majExt ω u)⁻¹) := cont_inv hωc hωpos
  have hI : Integrable (fun u : ℝ => (majExt ω u)⁻¹)
      (volume.restrict (Icc (1 : ℝ) ((n : ℝ) + 1))) :=
    (hg.continuousOn).integrableOn_compact isCompact_Icc
  have h0 : 0 ≤ᵐ[volume.restrict (Icc (1 : ℝ) ((n : ℝ) + 1))]
      fun u => (majExt ω u)⁻¹ :=
    ae_of_all _ fun u => inv_nonneg.mpr (le_of_lt (majExt.pos hωpos u))
  rw [osgExt, integral_of_le h1, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hI h0]

/-- **The divergence leg.**  The crown's Osgood divergence
`(∫⁻ u in Ici 1, ENNReal.ofReal ((ω u)⁻¹)) = ⊤` forces the extended Osgood
transform `osgExt (majExt ω)` to `∞` at `∞`.  This is exactly the hypothesis
`exists_nnreal_bound_of_osgoodBarrier` asks for and which
`OsgoodUniformBound`'s header left unproven. -/
theorem tendsto_osgExt_majExt_atTop {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x)
    (hdiv : (∫⁻ u in Ici (1 : ℝ), ENNReal.ofReal ((ω u)⁻¹)) = ⊤) :
    Tendsto (osgExt (majExt ω)) atTop atTop := by
  -- the truncations are directed and cover `Ici 1` exactly
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Icc (1 : ℝ) ((n : ℝ) + 1)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro x hx
      refine ⟨hx.1, hx.2.trans ?_⟩
      exact_mod_cast Nat.succ_le_succ (Nat.le_max_left i j)
    · intro x hx
      refine ⟨hx.1, hx.2.trans ?_⟩
      exact_mod_cast Nat.succ_le_succ (Nat.le_max_right i j)
  have hunion : (⋃ n : ℕ, Icc (1 : ℝ) ((n : ℝ) + 1)) = Ici (1 : ℝ) := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨n, h1, _h2⟩
      exact h1
    · intro hu
      obtain ⟨n, hn⟩ := exists_nat_gt u
      exact ⟨n, hu, by linarith [hn]⟩
  -- continuity from below pushes `= ⊤` onto the truncations
  have hwf : ⨆ n : ℕ, ∫⁻ u in Icc (1 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ((ω u)⁻¹) = ⊤ := by
    rw [← setLIntegral_iUnion_of_directed _ hdir, hunion]
    exact hdiv
  have htop : ⨆ n : ℕ, ∫⁻ u in Icc (1 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ((majExt ω u)⁻¹) = ⊤ := by
    have hcong : ∀ n : ℕ,
        ∫⁻ u in Icc (1 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ((majExt ω u)⁻¹) =
          ∫⁻ u in Icc (1 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ((ω u)⁻¹) := fun n =>
      setLIntegral_congr_fun measurableSet_Icc fun u hu =>
        congr_arg ENNReal.ofReal (congr_arg Inv.inv
          (majExt_eq_on_Ici u (Set.mem_Ici.mpr hu.1)))
    rw [iSup_congr hcong, hwf]
  have hsup : ⨆ n : ℕ, ENNReal.ofReal (osgExt (majExt ω) ((n : ℝ) + 1)) = ⊤ :=
    (iSup_congr (ofReal_osgExt_majExt_eq_lintegral hωc hωpos)).trans htop
  -- an unbounded `ofReal`-image is an unbounded real sequence
  have hunb : ∀ R : ℝ, ∃ n : ℕ, R < osgExt (majExt ω) ((n : ℝ) + 1) := by
    intro R
    by_contra h
    push Not at h
    have hle : ⨆ n : ℕ, ENNReal.ofReal (osgExt (majExt ω) ((n : ℝ) + 1))
        ≤ ENNReal.ofReal R :=
      iSup_le fun n => ENNReal.ofReal_le_ofReal (h n)
    rw [hsup] at hle
    exact lt_irrefl (⊤ : ℝ≥0∞) (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  refine Filter.tendsto_atTop_atTop.mpr (fun b => ?_)
  obtain ⟨n, hn⟩ := hunb b
  exact ⟨(n : ℝ) + 1, fun v hv => le_of_lt
    (lt_of_lt_of_le hn (monotone_osgExt_majExt hωc hωpos hv))⟩

/-- **Uniform horizon-local Osgood cap with the crown's divergence hypothesis.**
One `M : ℝ≥0`, produced from `(b₀, T, ω)` before any unknown `y` is introduced,
bounds the barrier `b₀ + ∫₀ᵗ ω(y s) ds` on `(0, T)` for EVERY `y` that is
continuous, nonnegative and monotone on `[0, T]` and satisfies that integral
barrier.  This is `exists_nnreal_bound_of_osgoodBarrier` with the transform
divergence supplied by `tendsto_osgExt_majExt_atTop`, i.e. the form a consumer
holding only the `ENNReal` lintegral hypothesis can apply. -/
theorem exists_nnreal_bound_of_osgoodMajorant {b₀ T : ℝ} {ω : ℝ → ℝ}
    (hb₀ : 0 ≤ b₀) (hT : 0 < T)
    (hωc : ContinuousOn ω (Ici 0))
    (hωmono : MonotoneOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x)
    (hdiv : (∫⁻ u in Ici (1 : ℝ), ENNReal.ofReal ((ω u)⁻¹)) = ⊤) :
    ∃ M : NNReal, ∀ y : ℝ → ℝ, ContinuousOn y (Icc 0 T) →
      (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t) → MonotoneOn y (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, y t ≤ b₀ + ∫ s in (0)..t, ω (y s)) →
      ∀ t ∈ Ioo 0 T, b₀ + ∫ s in (0)..t, ω (y s) ≤ ↑M :=
  exists_nnreal_bound_of_osgoodBarrier hb₀ hT hωc hωmono hωpos
    (tendsto_osgExt_majExt_atTop hωc hωpos hdiv)

end Navier.Analysis.OsgoodDivergenceBridge

#print axioms Navier.Analysis.OsgoodDivergenceBridge.ofReal_osgExt_majExt_eq_lintegral
#print axioms Navier.Analysis.OsgoodDivergenceBridge.tendsto_osgExt_majExt_atTop
#print axioms Navier.Analysis.OsgoodDivergenceBridge.exists_nnreal_bound_of_osgoodMajorant
