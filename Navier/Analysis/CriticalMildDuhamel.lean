import Navier.Analysis.ComplexFrequencyHeatLeray

/-!
# Complex Fourier triad Duhamel estimate

This module is the first time-integrated estimate for the actual projected
Navier--Stokes Fourier nonlinearity in the current complex frequency model.
For a real transport frequency `p`, the coefficient
`⟪p, v⟫ • w` is the Fourier transport interaction; the heat--Leray multiplier
is applied at the output frequency.  The bound below is a finite-dimensional
triad estimate, not a Fourier-transform, convolution, critical-space, or
fixed-point theorem.

Reference: T. Kato, *Strong `L^p`-solutions of the Navier--Stokes equation in
`R^m`*, Math. Z. 187 (1984), §2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory intervalIntegral

namespace Navier.Analysis.CriticalMildDuhamel

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray

/-- The projected Fourier transport interaction with real transport frequency
`p`.  The scalar is the Hermitian pairing with an embedded real vector, hence
it agrees with the usual bilinear coordinate coefficient in this setting. -/
def spectralTransport (p : Space) (v w : ComplexSpace) : ComplexSpace :=
  (inner ℂ (complexFrequency p) (complexEuclideanPoint v)) • w

/-- The Duhamel contribution of one ordered Fourier triad.  The output mode is
`k`; a full Fourier convolution must still sum these interactions over all
input pairs with `p + q = k`. -/
def spectralDuhamel (ν : ℝ) (k p : Space) (t : ℝ)
    (v w : ℝ → ComplexSpace) : ComplexE3 :=
  ∫ s in (0 : ℝ)..t,
    complexEuclideanPoint
      (complexFrequencyHeatLeray ν (t - s) k
        (spectralTransport p (v s) (w s)))

/-- The Fourier transport interaction is bounded by its real frequency and
the Hermitian Euclidean norms of its two complex amplitudes. -/
theorem complexEuclideanNorm_spectralTransport_le
    (p : Space) (v w : ComplexSpace) :
    complexEuclideanNorm (spectralTransport p v w) ≤
      ‖complexFrequency p‖ * complexEuclideanNorm v * complexEuclideanNorm w := by
  unfold complexEuclideanNorm spectralTransport
  rw [complexEuclideanPoint_smul, norm_smul]
  calc
    ‖inner ℂ (complexFrequency p) (complexEuclideanPoint v)‖ *
          ‖complexEuclideanPoint w‖ ≤
        (‖complexFrequency p‖ * ‖complexEuclideanPoint v‖) *
          ‖complexEuclideanPoint w‖ := by
      exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = ‖complexFrequency p‖ * ‖complexEuclideanPoint v‖ *
          ‖complexEuclideanPoint w‖ := by ring

/-- Kato's first finite-dimensional Duhamel estimate for one actual Fourier
transport interaction.  The hypotheses bound the amplitudes on the oriented
integration interval, while `ν ≥ 0` makes the exact heat--Leray kernel a norm
contraction.  No critical-space or global a-priori bound is assumed. -/
theorem complexEuclideanNorm_spectralDuhamel_le
    {ν t V W : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hV : 0 ≤ V)
    (k p : Space) (v w : ℝ → ComplexSpace)
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) t, complexEuclideanNorm (v s) ≤ V)
    (hw : ∀ s ∈ Set.Icc (0 : ℝ) t, complexEuclideanNorm (w s) ≤ W)
    (hintegrable : IntervalIntegrable
      (fun s => complexEuclideanPoint
        (complexFrequencyHeatLeray ν (t - s) k
          (spectralTransport p (v s) (w s)))) volume 0 t) :
    ‖spectralDuhamel ν k p t v w‖ ≤
      ‖complexFrequency p‖ * V * W * |t| := by
  unfold spectralDuhamel
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖complexEuclideanPoint
          (complexFrequencyHeatLeray ν (t - s) k
            (spectralTransport p (v s) (w s)))‖ ≤
        ‖complexFrequency p‖ * V * W := by
    intro s hs
    have hts : 0 ≤ t - s := by
      exact sub_nonneg.mpr hs.2
    calc
      ‖complexEuclideanPoint
          (complexFrequencyHeatLeray ν (t - s) k
            (spectralTransport p (v s) (w s)))‖ =
          complexEuclideanNorm
            (complexFrequencyHeatLeray ν (t - s) k
              (spectralTransport p (v s) (w s))) := rfl
      _ ≤ complexEuclideanNorm (spectralTransport p (v s) (w s)) :=
        complexEuclideanNorm_complexFrequencyHeatLeray_le hν hts k _
      _ ≤ ‖complexFrequency p‖ * V * W := by
        refine le_trans (complexEuclideanNorm_spectralTransport_le p (v s) (w s)) ?_
        have hp : 0 ≤ ‖complexFrequency p‖ := norm_nonneg _
        calc
          ‖complexFrequency p‖ * complexEuclideanNorm (v s) *
              complexEuclideanNorm (w s) ≤
            ‖complexFrequency p‖ * V * complexEuclideanNorm (w s) := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left (hv s hs) hp
          _ ≤ ‖complexFrequency p‖ * V * W := by
              exact mul_le_mul_of_nonneg_left (hw s hs) (mul_nonneg hp hV)
  calc
    ‖∫ s in (0 : ℝ)..t,
        complexEuclideanPoint
          (complexFrequencyHeatLeray ν (t - s) k
            (spectralTransport p (v s) (w s)))‖ ≤
        ∫ s in (0 : ℝ)..t,
          ‖complexEuclideanPoint
            (complexFrequencyHeatLeray ν (t - s) k
              (spectralTransport p (v s) (w s)))‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ _s in (0 : ℝ)..t, ‖complexFrequency p‖ * V * W :=
      intervalIntegral.integral_mono_on ht hintegrable.norm
        intervalIntegral.intervalIntegrable_const hpoint
    _ = ‖complexFrequency p‖ * V * W * |t| := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [sub_zero, abs_of_nonneg ht]
      ring

end Navier.Analysis.CriticalMildDuhamel
