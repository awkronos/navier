/-
Adapted from OpenAI/NavierStokesAndEuler, revision
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, under Apache-2.0.
Upstream source: NavierStokes/R3/LpNormTools.lean
Changes: native module namespace; further compatibility edits are in Git history.
License: references/licenses/OpenAI-Apache-2.0.txt.
-/
import Navier.Construction.R3.ComparisonSetup

/-!
# Real-valued whole-space `Lᵖ` norms

These lemmas convert extended `Lᵖ` seminorms to the real-valued norms used by
the comparison argument. Bounds that require a finite right-hand norm retain
an explicit `MemLp` hypothesis.
-/


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Navier.ConstructionR3.LpNormTools

open ProblemStatement Comparison

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem lpNorm_nonneg (p : ℝ≥0∞) (f : Space → E) : 0 ≤ comparisonLpNorm p f :=
  ENNReal.toReal_nonneg

theorem lpNorm_congr_ae {p : ℝ≥0∞} {f g : Space → E}
    (hfg : f =ᵐ[volume] g) : comparisonLpNorm p f = comparisonLpNorm p g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

theorem lpNorm_mono_of_norm_le_ae {p : ℝ≥0∞} {f : Space → E} {g : Space → F}
    (hg : MemLp g p volume) (hfg : ∀ᵐ x ∂volume, ‖f x‖ ≤ ‖g x‖) :
    comparisonLpNorm p f ≤ comparisonLpNorm p g := by
  -- mathlib drift (pin 1f414401): `MeasureTheory.eLpNorm_mono_ae` gained a leading
  -- `hf : AEStronglyMeasurable f μ`. No measurability is available for `f` here, so
  -- split on it: the measurable branch is the original argument, and the
  -- non-measurable branch is vacuous since `MeasureTheory.eLpNorm_of_not_aestronglyMeasurable`
  -- makes the seminorm `∞`, whose `ENNReal.toReal` is `0`.
  by_cases hfm : AEStronglyMeasurable f volume
  · rw [comparisonLpNorm]
    exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne (eLpNorm_mono_ae hfm hfg)
  · rw [comparisonLpNorm, eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.toReal_top]
    exact ENNReal.toReal_nonneg

theorem lpNorm_mono_of_norm_le {p : ℝ≥0∞} {f : Space → E} {g : Space → F}
    (hg : MemLp g p volume) (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    comparisonLpNorm p f ≤ comparisonLpNorm p g :=
  lpNorm_mono_of_norm_le_ae hg (Filter.Eventually.of_forall hfg)

theorem lpNorm_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f g : Space → E}
    (hf : MemLp f p volume) (hg : MemLp g p volume) :
    comparisonLpNorm p (fun x => f x + g x) ≤ comparisonLpNorm p f + comparisonLpNorm p g := by
  calc
    comparisonLpNorm p (fun x => f x + g x) ≤
        (eLpNorm f p volume + eLpNorm g p volume).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩)
        -- mathlib drift (pin 1f414401): `MeasureTheory.eLpNorm_add_le`
        -- (LpSeminorm/TriangleInequality.lean) now takes only `hp1 : 1 ≤ p`; it
        -- discharges both `AEStronglyMeasurable` arguments internally, so the
        -- two leading measurability arguments are dropped.
        (eLpNorm_add_le hp1)
    _ = comparisonLpNorm p f + comparisonLpNorm p g :=
      ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne

theorem lpNorm_const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (p : ℝ≥0∞) (c : 𝕜) (f : Space → E) :
    comparisonLpNorm p (fun x => c • f x) = ‖c‖ * comparisonLpNorm p f := by
  change (eLpNorm (c • f) p volume).toReal = ‖c‖ * (eLpNorm f p volume).toReal
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm]

theorem lpNorm_one_eq_integral_norm {f : Space → E} (hf : Integrable f volume) :
    comparisonLpNorm 1 f = ∫ x : Space, ‖f x‖ := by
  -- mathlib drift (pin 1f414401): `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`
  -- (LpSeminorm/Defs.lean) now takes `hf : AEStronglyMeasurable f μ`.
  rw [comparisonLpNorm, eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]

theorem lpNorm_two_sq_eq_l2Sq [InnerProductSpace ℝ E] {f : Space → E}
    (hf : MemLp f 2 volume) : comparisonLpNorm 2 f ^ 2 = l2Sq f := by
  calc
    comparisonLpNorm 2 f ^ 2 = ‖hf.toLp f‖ ^ 2 := by rw [Lp.norm_toLp]; rfl
    _ = @inner ℝ _ _ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x : Space, @inner ℝ _ _ ((hf.toLp f) x) ((hf.toLp f) x) :=
      L2.inner_def _ _
    _ = l2Sq f := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]

theorem lpNorm_two_eq_sqrt_l2Sq [InnerProductSpace ℝ E] {f : Space → E}
    (hf : MemLp f 2 volume) : comparisonLpNorm 2 f = Real.sqrt (l2Sq f) := by
  rw [← lpNorm_two_sq_eq_l2Sq hf, Real.sqrt_sq (lpNorm_nonneg 2 f)]

end Navier.ConstructionR3.LpNormTools

-- rc4 era-heal receipts (heal-navier-1017): the three theorems whose proofs changed.
#print axioms Navier.ConstructionR3.LpNormTools.lpNorm_mono_of_norm_le_ae
#print axioms Navier.ConstructionR3.LpNormTools.lpNorm_add_le
#print axioms Navier.ConstructionR3.LpNormTools.lpNorm_one_eq_integral_norm
