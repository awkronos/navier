import Navier.Analysis.CriticalMildDuhamel

/-!
# Finite complex Fourier convolution for the mild layer

This module sums the concrete projected Fourier transport interaction over a
finite retained frequency set.  It records exactly the finite convolution
bound needed before a genuine Fourier-series or critical Banach-space limit can
be attempted.  It is not a whole-space Fourier transform or a PDE solution.

Reference: T. Kato, *Strong `L^p`-solutions of the Navier--Stokes equation in
`R^m`*, Math. Z. 187 (1984), §2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CriticalMildConvolution

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel

/-- The finite Fourier convolution of the actual transport interaction.  For
an ordered pair of retained modes `(i,j)`, the `j`th frequency transports the
`i`th amplitude and the contribution is retained exactly when its output is
the selected mode `k`. -/
def spectralConvolution {n : ℕ} (q : Fin n → Space)
    (v w : Fin n → ComplexSpace) (k : Fin n) : ComplexE3 :=
  ∑ i : Fin n, ∑ j : Fin n,
    if q i + q j = q k then
      complexEuclideanPoint (spectralTransport (q j) (v i) (w j))
    else 0

/-- The norm of the retained complex Fourier convolution is bounded by its
literal scalar convolution.  No infinite summation or summability assumption
is hidden in this finite statement. -/
theorem norm_spectralConvolution_le {n : ℕ} (q : Fin n → Space)
    (v w : Fin n → ComplexSpace) (k : Fin n) :
    ‖spectralConvolution q v w k‖ ≤
      ∑ i : Fin n, ∑ j : Fin n,
        if q i + q j = q k then
          ‖complexFrequency (q j)‖ * complexEuclideanNorm (v i) *
            complexEuclideanNorm (w j)
        else 0 := by
  unfold spectralConvolution
  calc
    ‖∑ i : Fin n, ∑ j : Fin n,
        if q i + q j = q k then
          complexEuclideanPoint (spectralTransport (q j) (v i) (w j))
        else 0‖ ≤
      ∑ i : Fin n, ‖∑ j : Fin n,
        if q i + q j = q k then
          complexEuclideanPoint (spectralTransport (q j) (v i) (w j))
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖if q i + q j = q k then
          complexEuclideanPoint (spectralTransport (q j) (v i) (w j))
        else 0‖ := by
      exact Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        if q i + q j = q k then
          ‖complexFrequency (q j)‖ * complexEuclideanNorm (v i) *
            complexEuclideanNorm (w j)
        else 0 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      split_ifs with hij
      · simpa [complexEuclideanNorm] using
          complexEuclideanNorm_spectralTransport_le (q j) (v i) (w j)
      · simp

/-- Explicit continuous amplitudes make the exact single-triad Duhamel
integrand interval-integrable.  This is the non-vacuity producer consumed by
`complexEuclideanNorm_spectralDuhamel_le`; it does not postulate
integrability as a fixed-point payload. -/
theorem spectralDuhamel_intervalIntegrable_of_continuous
    (ν t : ℝ) (k p : Space) (v w : ℝ → ComplexSpace)
    (hv : Continuous v) (hw : Continuous w) :
    IntervalIntegrable
      (fun s => complexEuclideanPoint
        (complexFrequencyHeatLeray ν (t - s) k
          (spectralTransport p (v s) (w s)))) volume 0 t := by
  apply Continuous.intervalIntegrable
  have hvE : Continuous fun s => complexEuclideanPoint (v s) :=
    (PiLp.continuous_toLp 2 _).comp hv
  have hscalar : Continuous fun s =>
      inner ℂ (complexFrequency p) (complexEuclideanPoint (v s)) :=
    continuous_const.inner hvE
  have htransport : Continuous fun s => spectralTransport p (v s) (w s) := by
    unfold spectralTransport
    exact hscalar.smul hw
  have hheat : Continuous fun s : ℝ => complexHeatDecay ν (t - s) k := by
    unfold complexHeatDecay Navier.Analysis.FrequencyHeatLeray.heatDecay
    fun_prop
  have htransportE : Continuous fun s =>
      complexEuclideanPoint (spectralTransport p (v s) (w s)) :=
    (PiLp.continuous_toLp 2 _).comp htransport
  have hheatC : Continuous fun s : ℝ => (complexHeatDecay ν (t - s) k : ℂ) :=
    Complex.continuous_ofReal.comp hheat
  have hkernelE : Continuous fun s =>
      (complexHeatDecay ν (t - s) k : ℂ) •
        complexEuclideanLeray k
          (complexEuclideanPoint (spectralTransport p (v s) (w s))) :=
    hheatC.smul ((complexEuclideanLeray k).continuous.comp htransportE)
  simp_rw [complexEuclideanPoint_complexFrequencyHeatLeray]
  exact hkernelE

/-- The triad Duhamel estimate consumes the integrability produced by
continuous amplitudes.  The amplitude bounds remain explicit rather than being
packaged as a local-solution or contraction hypothesis. -/
theorem norm_spectralDuhamel_le_of_continuous
    {ν t V W : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hV : 0 ≤ V)
    (k p : Space) (v w : ℝ → ComplexSpace)
    (hv : Continuous v) (hw : Continuous w)
    (hvb : ∀ s ∈ Set.Icc (0 : ℝ) t, complexEuclideanNorm (v s) ≤ V)
    (hwb : ∀ s ∈ Set.Icc (0 : ℝ) t, complexEuclideanNorm (w s) ≤ W) :
    ‖spectralDuhamel ν k p t v w‖ ≤
      ‖complexFrequency p‖ * V * W * |t| :=
  complexEuclideanNorm_spectralDuhamel_le hν ht hV k p v w hvb hwb
    (spectralDuhamel_intervalIntegrable_of_continuous ν t k p v w hv hw)

end Navier.Analysis.CriticalMildConvolution
