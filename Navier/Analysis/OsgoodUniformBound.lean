import Mathlib

/-!
# Uniform horizon-local Osgood bound (the §4 premise `CrownBridgeReduction` needs)

**Why this module exists.**  `Navier.Analysis.CrownBridgeReduction` §4
(`horizonLocal_of_osgoodEnvelopeMajorant`, sorried at this revision) must
produce

    ∃ M : ℝ≥0, ∀ u p, (u 0 = u₀) → SolvesBefore ν T u p → h3EnvelopeControl T u ≤ M

for a FIXED horizon `T`: the bound may depend on `ν`, `u₀`, `T` and on the
majorant `ω` that `OsgoodEnvelopeMajorant` supplies, but it must NOT depend on
the solution `u`.  The §3 leaf `exists_le_of_osgoodMajorant` (closed at
`2c8572d`) returns `∃ M, ∀ t ∈ Icc 0 T, y t ≤ M` for ONE given `y`; consuming it
solution-by-solution produces an `M` that varies with `u`, so it cannot discharge
the `∃ M, ∀ u p` quantifier block.  What §4 needs is therefore a bound on the
barrier, uniform over the whole family of admissible unknowns sharing the datum
`b₀` and the majorant `ω`.  That is certified here
(`exists_nnreal_bound_of_osgoodBarrier`) — the classical Bihari/Osgood
comparison, stated in the uniform form §4 consumes.

## Certified here (no sorry)

* `majExt`, `majExt.continuous/pos/monotone` — a majorant that is continuous,
  positive and nondecreasing on `[0, ∞)` extended to all of `ℝ` by clamping its
  argument at `0`.  The extension is what makes the Osgood transform
  differentiable on the whole line, so the comparison uses only continuity of
  the data (no a.e. derivative→integral comparison, which this Mathlib revision
  does not carry — see the design note in the `CrownBridgeReduction` header).
* `osgExt`, `hasDerivAt_osgExt_majExt`, `deriv_osgExt_majExt`,
  `diff_osgExt_majExt`, `monotone_osgExt_majExt` — the transform
  `v ⟼ ∫ u in (1)..v, (·)⁻¹` of the extended majorant, its everywhere derivative
  `(majExt ω v)⁻¹`, and its monotonicity.
* `exists_nnreal_bound_of_osgoodBarrier` — the uniform bound.  Proof: clamp the
  unknown to `Icc 0 T`, set `f := majExt ω ∘ yb` and `V := b₀ + ∫₀ᵗ f`, so
  `V` is differentiable on `ℝ` with `V' = f` (`intervalIntegral.
  integral_hasDerivAt_right`, continuous data); `y ≤ V` on `(0,T)` is the
  barrier; then `t - osgExt (majExt ω) (V t)` has derivative
  `1 - f t / majExt ω (V t) ≥ 0` because `f t = majExt ω (yb t) ≤ majExt ω (V t)`
  (`monotoneOn_of_deriv_nonneg`), so `osgExt (majExt ω) (V t) ≤
  osgExt (majExt ω) b₀ + t` on the WHOLE horizon — anchored at `t = 0`, where
  `V 0 = b₀`, which is what makes the constant independent of `y`; one level
  `N` with `osgExt (majExt ω) N > osgExt (majExt ω) b₀ + T` then caps every
  barrier value.

## What this module does NOT close

The single remaining bridge to §4 is measure-theoretic, not analytic:
`OsgoodEnvelopeMajorant` supplies the divergence as
`∫⁻ u in Ici 1, ENNReal.ofReal ((ω u)⁻¹) = ⊤`, whereas this leaf takes the
equivalent-for-continuous-data form `Tendsto (osgExt (majExt ω)) atTop atTop`
(`hGtop`).  The bridge is a monotone-convergence argument — the disjoint
annuli `Ioc (n+1) (n+2)` cover `Ioi 1`, `MeasureTheory.lintegral_iUnion` turns
the divergence into a divergent `tsum` of truncations, and
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` identifies each truncation
with `ENNReal.ofReal (∫ u in (1)..v, (majExt ω u)⁻¹)`.  It is recorded as a
named obligation rather than assumed away: no result here is wrapped as its own
hypothesis.  With that bridge, §4 follows by taking
`y t := (h3EnvelopeControl t u).toReal` (nonnegative, since `ENNReal.toReal ≥ 0`),
`b₀ := (h3EnvelopeBudget (u 0)).toReal` (independent of `u` because the initial
condition forces `u 0 = u₀`), and descending `h3EnvelopeControl t u ≤
ENNReal.ofReal (barrier t)` through `h3EnvelopeControl_mono` at interior times.

Prior art consumed, not restated: the §3/§4 statement shapes, the trap-majorant
divergence `lintegral_trapMajorant_inv` (closed at `06f3aa3`), and
`h3EnvelopeControl_mono` / `h3EnvelopeBudget_le_h3EnvelopeControl` in
`Navier/Analysis/CrownBridgeReduction.lean`; `osgoodG` there is the unextended
transform, which agrees with `osgExt (majExt ω)` on `Ici 1` — this module keeps
the extension explicit instead of editing that file.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped ENNReal Topology MeasureTheory
open Set Filter MeasureTheory intervalIntegral

noncomputable section

namespace Navier.Analysis.OsgoodUniformBound


/-- navier `CrownBridgeReduction.osgoodG`, restated here for development. -/
def osgExt (ω : ℝ → ℝ) (v : ℝ) : ℝ := ∫ u in (1:ℝ)..v, (ω u)⁻¹

/-- A majorant extended to all of `ℝ` by clamping its argument at `0`. -/
def majExt (ω : ℝ → ℝ) : ℝ → ℝ := fun x => ω (x ⊔ 0)

theorem majExt.continuous {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0)) :
    Continuous (majExt ω) :=
  continuousOn_univ.mp
    (hωc.comp (continuous_id.max continuous_const).continuousOn
      (fun s _ => mem_Ici.mpr (le_max_right s 0)))

theorem majExt.pos {ω : ℝ → ℝ} (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) (x : ℝ) :
    0 < majExt ω x := hωpos _ (le_max_right x 0)

theorem majExt.monotone {ω : ℝ → ℝ} (hωmono : MonotoneOn ω (Ici 0)) : Monotone (majExt ω) :=
  fun a b hab => hωmono (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)

theorem cont_inv {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) :
    Continuous (fun x => (majExt ω x)⁻¹) :=
  (majExt.continuous hωc).inv₀ (fun x => ne_of_gt (majExt.pos hωpos x))

/-- Derivative of the extended Osgood transform, everywhere on `ℝ`. -/
theorem hasDerivAt_osgExt_majExt {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) (v : ℝ) :
    HasDerivAt (osgExt (majExt ω)) ((majExt ω v)⁻¹) v :=
  integral_hasDerivAt_right ((cont_inv hωc hωpos).intervalIntegrable 1 v)
    ((cont_inv hωc hωpos).aestronglyMeasurable.stronglyMeasurableAtFilter)
    (cont_inv hωc hωpos).continuousAt

theorem diff_osgExt_majExt {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) :
    Differentiable ℝ (osgExt (majExt ω)) :=
  differentiable_integral_of_continuous (cont_inv hωc hωpos)

theorem deriv_osgExt_majExt {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) (v : ℝ) :
    deriv (osgExt (majExt ω)) v = (majExt ω v)⁻¹ := (hasDerivAt_osgExt_majExt hωc hωpos v).deriv

theorem monotone_osgExt_majExt {ω : ℝ → ℝ} (hωc : ContinuousOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x) : Monotone (osgExt (majExt ω)) :=
  monotone_of_deriv_nonneg (diff_osgExt_majExt hωc hωpos) fun v => by
    rw [deriv_osgExt_majExt hωc hωpos]
    exact inv_nonneg.mpr (le_of_lt (majExt.pos hωpos v))

/-- **Uniform horizon-local Osgood bound.**  For a fixed datum `b₀`, horizon `T`
and majorant `ω`, ONE constant `M : ℝ≥0` bounds the barrier
`b₀ + ∫₀ᵗ ω(y s) ds` on `(0,T)` for EVERY unknown `y` that is continuous and
nonnegative on `[0,T]`, monotone there, and satisfies the integral barrier with
that `b₀` and `ω`.  `M` is produced before `y` is introduced, which is exactly
the shape `HorizonLocalCriticalControl` needs: its `∃ M : ℝ≥0` sits BEFORE
`∀ u p`, so a per-solution existence statement (the §3 leaf
`exists_le_of_osgoodMajorant`, closed at `2c8572d`, whose witness is literally
`y T`) cannot discharge it. -/
theorem exists_nnreal_bound_of_osgoodBarrier {b₀ T : ℝ} {ω : ℝ → ℝ}
    (hb₀ : 0 ≤ b₀) (hT : 0 < T)
    (hωc : ContinuousOn ω (Ici 0))
    (hωmono : MonotoneOn ω (Ici 0))
    (hωpos : ∀ x ∈ Ici (0 : ℝ), 0 < ω x)
    (hGtop : Tendsto (osgExt (majExt ω)) atTop atTop) :
    ∃ M : NNReal, ∀ y : ℝ → ℝ, ContinuousOn y (Icc 0 T) →
      (∀ t ∈ Icc (0:ℝ) T, 0 ≤ y t) → MonotoneOn y (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, y t ≤ b₀ + ∫ s in (0)..t, ω (y s)) →
      ∀ t ∈ Ioo 0 T, b₀ + ∫ s in (0)..t, ω (y s) ≤ ↑M := by
  -- the clamp depends on the horizon only
  set e : ℝ → ℝ := fun s => max (min s T) 0 with he_def
  have he_cont : Continuous e := (continuous_id.min continuous_const).max continuous_const
  have he_mono : Monotone e := fun a b hab => max_le_max (min_le_min hab le_rfl) le_rfl
  have he_mem : ∀ s, e s ∈ Icc (0:ℝ) T := fun s =>
    ⟨le_max_right (min s T) 0, max_le (min_le_right s T) hT.le⟩
  have he_id : ∀ t ∈ Icc (0:ℝ) T, e t = t := fun t ht =>
    (max_eq_left (le_min ht.1 (le_trans ht.1 ht.2))).trans (min_eq_left ht.2)
  -- the cap: one level above the datum-and-horizon bound of the transform
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hGtop.eventually (eventually_gt_atTop (osgExt (majExt ω) b₀ + T)))
  refine ⟨⟨max (N : ℝ) 0, le_max_right N 0⟩, ?_⟩
  -- now let y be ANY admissible unknown
  intro y hyc hynn hymon hmaj t ht
  have hIcc : t ∈ Icc (0:ℝ) T := ⟨ht.1.le, ht.2.le⟩
  set yb : ℝ → ℝ := fun s => y (e s) with yb_def
  have hyb_cont : Continuous yb :=
    continuousOn_univ.mp (hyc.comp he_cont.continuousOn (fun s _ => he_mem s))
  have hyb_nonneg : ∀ s, 0 ≤ yb s := fun s => hynn _ (he_mem s)
  have hyb_mono : Monotone yb := fun a b hab => hymon (he_mem a) (he_mem b) (he_mono hab)
  have hyb_eq : ∀ t ∈ Icc (0:ℝ) T, yb t = y t := fun t ht => congr_arg y (he_id t ht)
  set f : ℝ → ℝ := fun s => majExt ω (yb s) with f_def
  have hf_eq : ∀ t ∈ Icc (0:ℝ) T, f t = ω (y t) := fun t ht => by
    show majExt ω (yb t) = ω (y t)
    rw [hyb_eq t ht, show majExt ω (y t) = ω (y t ⊔ 0) from rfl, max_eq_left (hynn t ht)]
  have hf_cont : Continuous f := (majExt.continuous hωc).comp hyb_cont
  have hf_pos : ∀ s, 0 < f s := fun s => majExt.pos hωpos (yb s)
  have hf_mono : Monotone f := majExt.monotone hωmono |>.comp hyb_mono
  set V : ℝ → ℝ := fun tt => b₀ + ∫ s in (0)..tt, f s with V_def
  have hV_diff : Differentiable ℝ V :=
    (differentiable_const b₀).add (differentiable_integral_of_continuous hf_cont)
  have hV_has : ∀ tt, HasDerivAt V (f tt) tt := fun tt => by
    change HasDerivAt (fun u : ℝ => b₀ + ∫ s in (0)..u, f s) (f tt) tt
    convert ((hasDerivAt_const tt b₀).add (integral_hasDerivAt_right
      (hf_cont.intervalIntegrable 0 tt) (hf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter)
      hf_cont.continuousAt)) using 1
    · ring
  have hV_deriv : ∀ tt, deriv V tt = f tt := fun tt => (hV_has tt).deriv
  have hyV : ∀ tt ∈ Ioo (0:ℝ) T, yb tt ≤ V tt := by
    intro tt htt
    have hIcct : tt ∈ Icc (0:ℝ) T := ⟨htt.1.le, htt.2.le⟩
    have hfg : ∫ s in (0)..tt, ω (y s) = ∫ s in (0)..tt, f s := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      have hms : 0 ≤ s ∧ s ≤ tt := by
        rcases Set.mem_uIcc.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨ha, hb⟩
        · have hle : tt ≤ (0:ℝ) := le_trans ha hb
          linarith [(Set.mem_Ioo.mp htt).1]
      exact (hf_eq s ⟨hms.1, hms.2.trans hIcct.2⟩).symm
    calc yb tt = y tt := hyb_eq tt hIcct
      _ ≤ b₀ + ∫ s in (0)..tt, ω (y s) := hmaj tt htt
      _ = b₀ + ∫ s in (0)..tt, f s := congr_arg (b₀ + ·) hfg
      _ = V tt := rfl
  have hGcomp_diff : Differentiable ℝ (fun tt => osgExt (majExt ω) (V tt)) :=
    (diff_osgExt_majExt hωc hωpos).comp hV_diff
  have hderiv_le : ∀ tt ∈ Ioo (0:ℝ) T,
      0 ≤ deriv (fun x => x - osgExt (majExt ω) (V x)) tt := by
    intro tt htt
    have hpos : 0 < majExt ω (V tt) := majExt.pos hωpos _
    have hd : HasDerivAt (fun x : ℝ => x - osgExt (majExt ω) (V x))
        (1 - (majExt ω (V tt))⁻¹ * f tt) tt :=
      (hasDerivAt_id tt).sub ((hasDerivAt_osgExt_majExt hωc hωpos (V tt)).comp tt (hV_has tt))
    rw [hd.deriv, sub_nonneg, inv_mul_le_iff₀ hpos, mul_one]
    exact majExt.monotone hωmono (hyV tt htt)
  have hmono : MonotoneOn (fun tt => tt - osgExt (majExt ω) (V tt)) (Icc (0:ℝ) T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) T)
      ((differentiable_id.sub hGcomp_diff).continuous.continuousOn)
      ((differentiable_id.sub hGcomp_diff).differentiableOn)
      (fun tt htt => hderiv_le tt (by rw [interior_Icc] at htt; exact htt))
  have hV0 : V 0 = b₀ := by simp [V_def]
  have hkey : ∀ tt ∈ Icc (0:ℝ) T, osgExt (majExt ω) (V tt) ≤ osgExt (majExt ω) b₀ + tt := by
    intro tt htt
    have hle := hmono ⟨le_refl 0, hT.le⟩ htt htt.1
    dsimp only at hle
    rw [hV0, zero_sub] at hle
    linarith
  have hGN : osgExt (majExt ω) b₀ + T < osgExt (majExt ω) N := hN N (le_refl N)
  have hcap : osgExt (majExt ω) (V t) ≤ osgExt (majExt ω) b₀ + T :=
    (hkey t hIcc).trans (add_le_add_right ht.2.le _)
  have hVt : V t ≤ N := by
    by_contra h
    push Not at h
    linarith [hcap, monotone_osgExt_majExt hωc hωpos (le_of_lt h), hGN]
  have hfg : ∫ s in (0)..t, ω (y s) = ∫ s in (0)..t, f s := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hms : 0 ≤ s ∧ s ≤ t := by
      rcases Set.mem_uIcc.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨ha, hb⟩
      · have hle : t ≤ (0:ℝ) := le_trans ha hb
        linarith [ht.1]
    exact (hf_eq s ⟨hms.1, hms.2.trans ht.2.le⟩).symm
  calc b₀ + ∫ s in (0)..t, ω (y s) = b₀ + ∫ s in (0)..t, f s := congr_arg (b₀ + ·) hfg
    _ = V t := rfl
    _ ≤ (N : ℝ) := hVt
    _ ≤ max (N : ℝ) 0 := le_max_left N 0

end Navier.Analysis.OsgoodUniformBound

#print axioms Navier.Analysis.OsgoodUniformBound.exists_nnreal_bound_of_osgoodBarrier
