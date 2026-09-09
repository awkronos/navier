import Navier.Analysis.WholeSpaceSolenoidalHeatDomination
import Navier.Analysis.CurlDerivativeBridge

/-!
# Gaussian domination for the whole-space solenoidal cutoff

The pressure-free whole-space evolution is tested against
`curl (chi_R G a)`.  This file supplies the first missing limit input for that
exact test: a uniform, integrable Gaussian envelope for the field itself and
the resulting convergence of its momentum pairing on every finite-energy
solution slice.

The envelope retains both Gaussian scales created by the product rule.  The
cutoff-gradient correction is controlled by `G_tau`; the derivative of the
Gaussian is controlled by `G_(2 tau)`.  No spatial boundedness or decay of the
solution is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval BigOperators Matrix
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CurlDerivativeBridge
open Navier.Analysis.CurlIdentities
open Navier.Analysis.Vorticity
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatDomination
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.LocalEnstrophyBalance
open Navier.Analysis.ParabolicCaccioppoli

/-- The uncut solenoidal backward-heat field approached by the compact tests. -/
def backwardHeatCurlField
    (κ τ : ℝ) (x₀ a : Space) : Space → Space :=
  fun y => staticCurl (backwardHeatPotential κ τ x₀ a) y

/-- The uncut backward-heat curl paired with one velocity slice. -/
def backwardHeatCurlMomentum
    (κ τ : ℝ) (x₀ a : Space) (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, ∫ y : Space, backwardHeatCurlField κ τ x₀ a y j * u t y j

private theorem officialEuclideanNorm_staticGradient_le_of_components
    (f : Space → ℝ) (y : Space) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i : Fin 3, |fderiv ℝ f y (basisVector i)| ≤ B) :
    officialEuclideanNorm (staticGradient f y) ≤ Real.sqrt 3 * B := by
  refine (officialEuclideanNorm_le _).trans ?_
  exact mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg hB).2 (fun i => by
      simpa [staticGradient, Real.norm_eq_abs] using h i))
    (Real.sqrt_nonneg 3)

private theorem backwardHeatCurlField_eq_gradient_cross
    (κ τ : ℝ) (x₀ a y : Space) :
    backwardHeatCurlField κ τ x₀ a y =
      staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y ⨯₃ a := by
  unfold backwardHeatCurlField backwardHeatPotential
  rw [staticCurl_smul]
  · simp [staticCurl, fderiv_const_apply]
  · exact ((heatKernel_translate_contDiff κ τ x₀).differentiable
      (by norm_num)).differentiableAt
  · exact differentiableAt_const a

/-- **The actual mixed Gaussian envelope.**  Uniformly for `R >= 1`, the
physical field `curl (chi_R G_tau a)` is dominated by the sum of a `G_tau`
envelope (the `D chi_R` correction) and a `G_(2 tau)` envelope (the surviving
Gaussian derivative).  Both constants are independent of `R`, `x₀`, and `a`.
-/
theorem exists_solenoidalCutoffField_gaussian_envelope
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 < D ∧
      ∀ {R : ℝ}, 1 ≤ R → ∀ (x₀ a y : Space),
        officialEuclideanNorm
            (solenoidalCutoffField R (backwardHeatPotential κ τ x₀ a) y) ≤
          (Real.sqrt 3 * M * heatKernel κ τ (x₀ - y) +
            Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y)) *
              officialEuclideanNorm a := by
  obtain ⟨M, hM0, hM⟩ := exists_scaledCutoff_gradient_component_bound
  obtain ⟨D, hD0, hD⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  refine ⟨M, D, hM0, hD0, ?_⟩
  intro R hR x₀ a y
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRinv : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
  have hgradCutoff : officialEuclideanNorm (staticGradient (scaledCutoff R) y) ≤
      Real.sqrt 3 * M := by
    have hsmall := officialEuclideanNorm_staticGradient_le_of_components
      (scaledCutoff R) y (mul_nonneg (inv_nonneg.mpr hR0.le) hM0)
      (fun i => hM hR0 y i)
    exact hsmall.trans <| mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left hM0 hRinv) (Real.sqrt_nonneg 3)
  have hG0 : 0 ≤ heatKernel κ τ (x₀ - y) := heatKernel_nonneg hκ hτ _
  have hG20 : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
    heatKernel_nonneg hκ (by positivity) _
  have hA : officialEuclideanNorm (backwardHeatPotential κ τ x₀ a y) =
      heatKernel κ τ (x₀ - y) * officialEuclideanNorm a := by
    change ‖heatKernel κ τ (x₀ - y) • officialEuclideanPoint a‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hG0]
    rfl
  have hgradG : officialEuclideanNorm
      (staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y) ≤
        Real.sqrt 3 * (D * heatKernel κ (2 * τ) (x₀ - y)) := by
    apply officialEuclideanNorm_staticGradient_le_of_components _ _
      (mul_nonneg hD0.le hG20)
    intro i
    simpa [norm_basisVector] using hD x₀ y (basisVector i)
  have hcurl : officialEuclideanNorm (backwardHeatCurlField κ τ x₀ a y) ≤
      Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
        officialEuclideanNorm a := by
    rw [backwardHeatCurlField_eq_gradient_cross]
    exact (officialEuclideanNorm_cross_le _ _).trans <| by
      calc
        officialEuclideanNorm
              (staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y) *
            officialEuclideanNorm a ≤
          (Real.sqrt 3 * (D * heatKernel κ (2 * τ) (x₀ - y))) *
            officialEuclideanNorm a :=
              mul_le_mul_of_nonneg_right hgradG
                (officialEuclideanNorm_nonneg _)
        _ = Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
            officialEuclideanNorm a := by ring
  rw [solenoidalCutoffField_eq _ _
    (backwardHeatPotential_contDiff κ τ x₀ a) y]
  change officialEuclideanNorm
      (staticGradient (scaledCutoff R) y ⨯₃
          backwardHeatPotential κ τ x₀ a y +
        scaledCutoff R y • backwardHeatCurlField κ τ x₀ a y) ≤ _
  calc
    officialEuclideanNorm
        (staticGradient (scaledCutoff R) y ⨯₃
            backwardHeatPotential κ τ x₀ a y +
          scaledCutoff R y • backwardHeatCurlField κ τ x₀ a y) ≤
      officialEuclideanNorm
          (staticGradient (scaledCutoff R) y ⨯₃
            backwardHeatPotential κ τ x₀ a y) +
            officialEuclideanNorm
          (scaledCutoff R y • backwardHeatCurlField κ τ x₀ a y) := by
            change ‖officialEuclideanPoint
                (staticGradient (scaledCutoff R) y ⨯₃
                  backwardHeatPotential κ τ x₀ a y) +
              officialEuclideanPoint
                (scaledCutoff R y • backwardHeatCurlField κ τ x₀ a y)‖ ≤ _
            exact norm_add_le _ _
    _ ≤ (Real.sqrt 3 * M) *
          (heatKernel κ τ (x₀ - y) * officialEuclideanNorm a) +
        1 * (Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
          officialEuclideanNorm a) := by
      apply add_le_add
      · exact (officialEuclideanNorm_cross_le _ _).trans
          (mul_le_mul hgradCutoff (le_of_eq hA)
            (officialEuclideanNorm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg 3) hM0))
      · change ‖scaledCutoff R y • officialEuclideanPoint
            (backwardHeatCurlField κ τ x₀ a y)‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (scaledCutoff_nonneg R y), one_mul]
        calc
          scaledCutoff R y *
              ‖officialEuclideanPoint (backwardHeatCurlField κ τ x₀ a y)‖ ≤
            scaledCutoff R y *
              (Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
                officialEuclideanNorm a) :=
              mul_le_mul_of_nonneg_left hcurl (scaledCutoff_nonneg R y)
          _ ≤ 1 * (Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
                officialEuclideanNorm a) :=
              mul_le_mul_of_nonneg_right (scaledCutoff_le_one R y)
                (mul_nonneg
                  (mul_nonneg
                    (mul_nonneg (Real.sqrt_nonneg 3) hD0.le) hG20)
                  (officialEuclideanNorm_nonneg a))
          _ = Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
                officialEuclideanNorm a := one_mul _
    _ = (Real.sqrt 3 * M * heatKernel κ τ (x₀ - y) +
          Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y)) *
            officialEuclideanNorm a := by ring

/-- The uncut backward-heat curl is smooth, so its pairing with a smooth
finite-energy solution slice is measurable. -/
theorem backwardHeatCurlField_contDiff
    (κ τ : ℝ) (x₀ a : Space) :
    ContDiff ℝ ∞ (backwardHeatCurlField κ τ x₀ a) := by
  unfold backwardHeatCurlField
  exact staticCurl_contDiff _ (backwardHeatPotential_contDiff κ τ x₀ a)

/-- The exact compact test family, made total in the radius parameter by the
cofinal positive radius `max 1 R`. -/
def atTopCompactBackwardHeatCurlTest
    (R κ τ : ℝ) (x₀ a : Space) : CompactSolenoidalTest :=
  compactBackwardHeatCurlTest (max 1 R)
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 R)) κ τ x₀ a

/-- **Finite-energy endpoint limit for the actual compact solenoidal test.**
At every time before breakdown, the momentum paired with
`curl (chi_R G_tau a)` converges to the momentum paired with the uncut
`curl (G_tau a)`.  The proof consumes the mixed Gaussian envelope above and
the `SolvesBefore` finite-energy field; no pointwise bound on the velocity is
used. -/
theorem solvesBefore_compactBackwardHeatCurlTestedMomentum_tendsto
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Filter.Tendsto
      (fun R : ℝ => testedMomentum
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t)
      Filter.atTop (nhds (backwardHeatCurlMomentum κ τ x₀ a u t)) := by
  have hu : ContDiff ℝ ∞ (u t) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      contDiffAt_spatial_slice_before hsol.classical.1 ht0 htT y
  have hu2 : Integrable (fun y : Space => ‖u t y‖ ^ 2) :=
    hsol.finite_energy t ht0 htT
  have huNormMeas : Measurable (fun y : Space => ‖u t y‖) :=
    hu.continuous.norm.measurable
  have huNormPow : Integrable (fun y : Space => |‖u t y‖| ^ (2 : ℝ)) := by
    convert hu2 using 1
    funext y
    rw [abs_of_nonneg (norm_nonneg _), Real.rpow_two]
  have hG1 : Integrable (fun y : Space =>
      heatKernel κ τ (x₀ - y) * ‖u t y‖) :=
    integrable_heatKernel_mul_of_integrable_rpow hκ hτ
      (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀
  have hG2 : Integrable (fun y : Space =>
      heatKernel κ (2 * τ) (x₀ - y) * ‖u t y‖) :=
    integrable_heatKernel_mul_of_integrable_rpow hκ (by positivity)
      (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀
  obtain ⟨M, D, hM0, hD0, henv⟩ :=
    exists_solenoidalCutoffField_gaussian_envelope hκ hτ
  let H : Space → ℝ := fun y =>
    (Real.sqrt 3 * M * officialEuclideanNorm a) *
        (heatKernel κ τ (x₀ - y) * ‖u t y‖) +
      (Real.sqrt 3 * D * officialEuclideanNorm a) *
        (heatKernel κ (2 * τ) (x₀ - y) * ‖u t y‖)
  have hHint : Integrable H := by
    have hleft : Integrable (fun y : Space =>
        (Real.sqrt 3 * M * officialEuclideanNorm a) *
          (heatKernel κ τ (x₀ - y) * ‖u t y‖)) :=
      hG1.const_mul (Real.sqrt 3 * M * officialEuclideanNorm a)
    have hright : Integrable (fun y : Space =>
        (Real.sqrt 3 * D * officialEuclideanNorm a) *
          (heatKernel κ (2 * τ) (x₀ - y) * ‖u t y‖)) :=
      hG2.const_mul (Real.sqrt 3 * D * officialEuclideanNorm a)
    exact hleft.add hright
  have hj : ∀ j : Fin 3, Filter.Tendsto
      (fun R : ℝ => ∫ y : Space,
        (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j * u t y j)
      Filter.atTop (nhds (∫ y : Space,
        backwardHeatCurlField κ τ x₀ a y j * u t y j)) := by
    intro j
    apply tendsto_integral_filter_of_dominated_convergence H
    · filter_upwards with R
      have hfield : ContDiff ℝ ∞ (fun y : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y) := by
        exact solenoidalCutoffField_contDiff (max 1 R)
          (backwardHeatPotential κ τ x₀ a)
          (backwardHeatPotential_contDiff κ τ x₀ a)
      exact (((continuous_apply j).comp hfield.continuous).mul
        ((continuous_apply j).comp hu.continuous)).aestronglyMeasurable
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with y
      have hfieldEq :
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y =
            solenoidalCutoffField R (backwardHeatPotential κ τ x₀ a) y := by
        change solenoidalCutoffField (max 1 R)
          (backwardHeatPotential κ τ x₀ a) y = _
        rw [max_eq_right hR]
      have hfieldEnv := henv hR x₀ a y
      have hcoord :
          |(atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j| ≤
            officialEuclideanNorm
              ((atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y) := by
        have hsup :
            |(atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j| ≤
              ‖(atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y‖ := by
          simpa [Real.norm_eq_abs] using
          norm_le_pi_norm
            ((atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y) j
        exact hsup.trans (norm_le_officialEuclideanNorm _)
      rw [Real.norm_eq_abs, abs_mul]
      have huj : |u t y j| ≤ ‖u t y‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (u t y) j
      calc
        |(atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j| *
            |u t y j| ≤
          officialEuclideanNorm
              ((atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y) *
            ‖u t y‖ :=
              mul_le_mul hcoord huj (abs_nonneg _)
                (officialEuclideanNorm_nonneg _)
        _ = officialEuclideanNorm
              (solenoidalCutoffField R
                (backwardHeatPotential κ τ x₀ a) y) * ‖u t y‖ := by
              rw [hfieldEq]
        _ ≤ (Real.sqrt 3 * M * heatKernel κ τ (x₀ - y) +
              Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y)) *
              officialEuclideanNorm a * ‖u t y‖ :=
            mul_le_mul_of_nonneg_right hfieldEnv (norm_nonneg _)
        _ = H y := by simp only [H]; ring
    · exact hHint
    · filter_upwards with y
      have hfield := solenoidalCutoffField_tendsto
        (backwardHeatPotential κ τ x₀ a)
        (backwardHeatPotential_contDiff κ τ x₀ a) y
      have hcomp : Filter.Tendsto
          (fun R : ℝ => solenoidalCutoffField R
            (backwardHeatPotential κ τ x₀ a) y j)
          Filter.atTop
          (nhds (backwardHeatCurlField κ τ x₀ a y j)) := by
        rw [tendsto_pi_nhds] at hfield
        simpa [backwardHeatCurlField] using hfield j
      have htotal : Filter.Tendsto
          (fun R : ℝ =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j)
          Filter.atTop
          (nhds (backwardHeatCurlField κ τ x₀ a y j)) := by
        apply hcomp.congr'
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
        rw [show (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y j =
            solenoidalCutoffField (max 1 R)
              (backwardHeatPotential κ τ x₀ a) y j from rfl,
          max_eq_right hR]
      exact htotal.mul_const (u t y j)
  unfold testedMomentum backwardHeatCurlMomentum cutoffMomentumCoordinate
  simpa using tendsto_finsetSum Finset.univ (fun j _ => hj j)

end Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination.exists_solenoidalCutoffField_gaussian_envelope
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination.solvesBefore_compactBackwardHeatCurlTestedMomentum_tendsto
