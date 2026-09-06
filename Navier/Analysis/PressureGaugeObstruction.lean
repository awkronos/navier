import Navier.Analysis.CriticalControlDecomposition

/-!
# A pressure-gauge obstruction to unrestricted continuation

The exact rejected continuation statement controls only velocity but demands
agreement of arbitrary pressures before the original horizon. Zero velocity
and spatially constant pressure `(1-t)⁻¹` solve the unforced PDE before
time one. Compactness rules out a continuous pressure extension through time
one. This refutes the old interface for every velocity quantity without
refuting global existence for its zero initial datum.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff

namespace Navier.Analysis.PressureGaugeObstruction

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition

def singularPressure : PressureEvolution := fun t _ => (1 - t)⁻¹

theorem singularPressure_smooth_before_one :
    SmoothPressureBefore 1 singularPressure := by
  intro z hz
  have hne : 1 - z.1 ≠ 0 := by linarith [hz.1.2]
  unfold singularPressure
  fun_prop

theorem zero_singularPressure_solves_before_one :
    OriginalSolvesBefore 1 1 (fun _ _ => 0) singularPressure := by
  refine ⟨contDiffOn_const, singularPressure_smooth_before_one, ?_, ?_⟩
  · intro t _ _ x
    simp [divergence, spatialDerivative]
  · intro t ht ht1 x
    have hpg : pressureGradient singularPressure t x = 0 := by
      funext i
      change (fderiv ℝ (fun _ : Space => (1 - t)⁻¹) x) (basisVector i) = 0
      simp
    simp [timeDerivative, convection, spatialDerivative, laplacian, zeroForce, hpg]

theorem singularPressure_has_no_smooth_extension
    {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ q : PressureEvolution,
      SmoothPressureBefore (1 + δ) q ∧ PressureAgreesBefore 1 singularPressure q := by
  rintro ⟨q, hqsm, hagree⟩
  have hcontinuous : ContinuousOn (fun t : ℝ => q t 0) (Set.Icc 0 1) := by
    exact hqsm.continuousOn.comp
      (Continuous.prodMk_left (0 : Space)).continuousOn
      (by
        intro t ht
        exact ⟨⟨ht.1, by linarith [ht.2, hδ]⟩, Set.mem_univ _⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcontinuous
  let A : ℝ := |M| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg M]
  let t : ℝ := 1 - A⁻¹
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rw [sub_nonneg, inv_le_one₀ hA]
    exact hA1
  have ht1 : t < 1 := by dsimp [t]; linarith [inv_pos.mpr hA]
  have hqt : q t 0 = A := by
    have ha := congrFun (hagree t ht0 ht1) (0 : Space)
    rw [← ha]
    dsimp [singularPressure, t]
    field_simp
    ring
  have hle : q t 0 ≤ M := hM (Set.mem_image_of_mem _ ⟨ht0, ht1.le⟩)
  rw [hqt] at hle
  dsimp [A] at hle
  linarith [le_abs_self M]

theorem not_rejectedSameGaugeContinuation
    (N : OriginalCriticalQuantity) : ¬ RejectedSameGaugeContinuationFromCriticalControl N := by
  intro hcont
  obtain ⟨δ, hδ, hstep⟩ := hcont 1 one_pos (N 1 (fun _ _ => 0))
  obtain ⟨u', p', hsol, _huagree, hpagree⟩ :=
    hstep (0 : SchwartzVelocity) ProblemStatements.divergenceFreeInitial_zero
      1 one_pos (fun _ _ => 0) singularPressure
      (by intro x; simp) zero_singularPressure_solves_before_one le_rfl
  exact singularPressure_has_no_smooth_extension hδ
    ⟨p', hsol.2.1, hpagree⟩

end Navier.Analysis.PressureGaugeObstruction

#print axioms Navier.Analysis.PressureGaugeObstruction.singularPressure_smooth_before_one
#print axioms Navier.Analysis.PressureGaugeObstruction.zero_singularPressure_solves_before_one
#print axioms Navier.Analysis.PressureGaugeObstruction.singularPressure_has_no_smooth_extension
#print axioms Navier.Analysis.PressureGaugeObstruction.not_rejectedSameGaugeContinuation
