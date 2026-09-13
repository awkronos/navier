import Navier.Analysis.ContinuousLeiLinPhysicalSmoothing

/-!
# Strict-past physical smoothing for the continuous Duhamel term

At observation time `t`, every source time in `[0, τ]` with `τ < t` has a
uniform positive heat lag.  Gaussian smoothing turns spacetime `X⁻¹` source
control on this strict-past interval into every Fourier moment.  Fubini passes
those moments through the time integral, and Fourier inversion gives a
spatially `C∞` physical coordinate.

This is the old-time half of the split-Duhamel regularity argument.  The
recent tail `[τ,t]` requires propagated source moments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinPhysicalSmoothing
theorem integrable_weighted_heat_on_strict_past
    (b : ℝ → ES → ℂ) (ν τ t : ℝ) (hν : 0 < ν) (hτt : τ < t) (n : ℕ)
    (hmeas : AEStronglyMeasurable (fun p : ES × ℝ => b p.2 p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ))))
    (hsrc : Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ * ‖b p.2 p.1‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))) :
    Integrable (fun p : ES × ℝ => (‖p.1‖ ^ n : ℝ) •
      heatMode ν (t - p.2) (b p.2) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ))) := by
  let μ := volume.restrict (Icc (0 : ℝ) τ)
  let k : ℕ := n + 1
  let a : ℝ := ν * (t - τ)
  let C : ℝ := (Real.sqrt (a / (k : ℝ)))⁻¹ ^ k
  have ha : 0 < a := mul_pos hν (sub_pos.mpr hτt)
  have hneξ : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton (μ := (volume : Measure ES)) (0 : ES))
  have hne : ∀ᵐ p : ES × ℝ ∂volume.prod μ, p.1 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · filter_upwards [hneξ] with ξ hξ
      exact Filter.Eventually.of_forall fun _ => hξ
    · exact (measurableSet_singleton (0 : ES)).compl.preimage measurable_fst
  have hmem : ∀ᵐ p : ES × ℝ ∂volume.prod μ, p.2 ∈ Icc (0 : ℝ) τ := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · exact Filter.Eventually.of_forall fun _ => ae_restrict_mem isClosed_Icc.measurableSet
    · exact isClosed_Icc.measurableSet.preimage measurable_snd
  have hmajor : ∀ᵐ p : ES × ℝ ∂volume.prod μ,
      ‖(‖p.1‖ ^ n : ℝ) • heatMode ν (t - p.2) (b p.2) p.1‖ ≤
        C * (‖p.1‖⁻¹ * ‖b p.2 p.1‖) := by
    filter_upwards [hne, hmem] with p hp hpt
    have hr : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    simp only [heatMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hdecay : Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2))) ≤
        Real.exp (-(a * ‖p.1‖ * ‖p.1‖)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      dsimp [a]
      have hlag : t - τ ≤ t - p.2 := sub_le_sub_left hpt.2 t
      nlinarith [mul_nonneg hν.le (sq_nonneg ‖p.1‖)]
    have hfirst : ‖p.1‖ ^ n *
        (Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2))) * ‖b p.2 p.1‖) ≤
        ‖p.1‖ ^ n *
          (Real.exp (-(a * ‖p.1‖ * ‖p.1‖)) * ‖b p.2 p.1‖) := by
      gcongr
    refine hfirst.trans ?_
    have heq : ‖p.1‖ ^ n *
        (Real.exp (-(a * ‖p.1‖ * ‖p.1‖)) * ‖b p.2 p.1‖) =
        (‖p.1‖ ^ k * Real.exp (-(a * ‖p.1‖ * ‖p.1‖))) *
          (‖p.1‖⁻¹ * ‖b p.2 p.1‖) := by
      dsimp [k]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (pow_mul_exp_neg_mul_sq_le ha (norm_nonneg p.1) k)
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  refine (hsrc.const_mul C).mono' ?_ hmajor
  have hmult : AEStronglyMeasurable (fun p : ES × ℝ =>
      ‖p.1‖ ^ n * Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2)))) (volume.prod μ) := by
    fun_prop
  exact (hmult.smul hmeas).congr (Filter.Eventually.of_forall fun p => by
    simp [heatMode, mul_assoc])

def continuousDuhamelBefore (ν τ : ℝ) (u v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ξ : ES) : ComplexSpace := fun i =>
  ∫ s in Icc (0 : ℝ) τ,
    heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i) ξ

theorem integrable_pow_norm_continuousDuhamelBefore
    (u v : ℝ → ES → ComplexSpace) (ν τ t : ℝ) (i : Fin 3) (n : ℕ)
    (hjoint : Integrable (fun p : ES × ℝ =>
      (‖p.1‖ ^ n : ℝ) • heatMode ν (t - p.2)
        (fun ζ : ES => continuousNavierSource u v p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))) :
    Integrable (fun ξ : ES =>
      ‖ξ‖ ^ n * ‖continuousDuhamelBefore ν τ u v t ξ i‖) := by
  set μ := volume.restrict (Icc (0 : ℝ) τ)
  have hi : Integrable (fun ξ : ES => ∫ s,
      (‖ξ‖ ^ n : ℝ) • heatMode ν (t - s)
        (fun ζ : ES => continuousNavierSource u v s ζ i) ξ ∂μ) :=
    hjoint.integral_prod_left
  refine hi.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖∫ s, (‖ξ‖ ^ n : ℝ) • heatMode ν (t - s)
      (fun ζ : ES => continuousNavierSource u v s ζ i) ξ ∂μ‖ =
    ‖ξ‖ ^ n * ‖continuousDuhamelBefore ν τ u v t ξ i‖
  rw [integral_smul, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  rfl

theorem contDiff_infty_physicalCoord_continuousDuhamelBefore
    (u v : ℝ → ES → ComplexSpace) (ν τ t : ℝ) (i : Fin 3)
    (hν : 0 < ν) (hτt : τ < t)
    (hmeas : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ))))
    (hsrc : Integrable (fun p : ES × ℝ =>
      ‖p.1‖⁻¹ * ‖continuousNavierSource u v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoord (continuousDuhamelBefore ν τ u v t) i) := by
  apply contDiff_infty_physicalCoord_of_integrable_moments
  intro n
  apply integrable_pow_norm_continuousDuhamelBefore u v ν τ t i n
  exact integrable_weighted_heat_on_strict_past
    (fun s ξ => continuousNavierSource u v s ξ i) ν τ t hν hτt n hmeas hsrc


end Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing

#check Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.integrable_weighted_heat_on_strict_past
#check Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.integrable_pow_norm_continuousDuhamelBefore
#check Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.contDiff_infty_physicalCoord_continuousDuhamelBefore

#print axioms Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.integrable_weighted_heat_on_strict_past
#print axioms Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.integrable_pow_norm_continuousDuhamelBefore
#print axioms Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing.contDiff_infty_physicalCoord_continuousDuhamelBefore
