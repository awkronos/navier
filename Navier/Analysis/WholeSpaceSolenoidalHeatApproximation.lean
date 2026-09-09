import Navier.Analysis.WholeSpaceCriticalEvolution
import Navier.Analysis.CurlIdentities
import Navier.Analysis.LocalEnstrophyBalance

/-!
# Divergence-preserving compact approximation of backward heat tests

Multiplying a solenoidal test by a scalar cutoff creates a divergence error.
The curl construction avoids that defect exactly.  For a smooth vector
potential `A`, set

`Phi_R = curl (chi_R A)`.

Every positive-radius `Phi_R` is smooth, compactly supported, and divergence
free on the native whole-space carrier.  The product rule gives

`Phi_R = grad chi_R x A + chi_R curl A`,

so the only cutoff correction carries an explicit `R^-1` derivative.  The
same construction is specialized below to a Gaussian backward-heat vector
potential and fed directly into the pressure-free local evolution theorem.

This does not identify a periodic lattice with `R^3`, and it does not assume a
global critical bound.  A later limit still has to dominate the displayed
correction and the differentiated test terms along the solution trajectory.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval BigOperators Matrix
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceSolenoidalHeatApproximation

open Navier
open Navier.Breakdown
open Navier.Analysis.Vorticity
open Navier.Analysis.CurlIdentities
open Navier.Analysis.LocalEnstrophyBalance
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WholeSpaceCriticalEvolution

/-- Curl-generated scalar cutoff of a vector potential.  Unlike direct
multiplication of a solenoidal field by `scaledCutoff`, this construction
preserves divergence exactly. -/
def solenoidalCutoffField (R : ℝ) (A : Space → Space) : Space → Space :=
  fun x => staticCurl (fun y => scaledCutoff R y • A y) x

theorem solenoidalCutoffField_contDiff
    (R : ℝ) (A : Space → Space) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (solenoidalCutoffField R A) := by
  apply staticCurl_contDiff
  exact (scaledCutoff_contDiff R).smul hA

/-- Curl differentiation does not enlarge support, so the positive-radius
curl cutoff is genuinely compactly supported. -/
theorem solenoidalCutoffField_hasCompactSupport
    {R : ℝ} (hR : 0 < R) (A : Space → Space) :
    HasCompactSupport (solenoidalCutoffField R A) := by
  let w : Space → Space := fun y => scaledCutoff R y • A y
  have hw : HasCompactSupport w := by
    exact (scaledCutoff_hasCompactSupport hR).smul_right
  have hterm : ∀ i : Fin 3, HasCompactSupport
      (fun x : Space => basisVector i ⨯₃ fderiv ℝ w x (basisVector i)) := by
    intro i
    exact (hw.fderiv_apply ℝ (basisVector i)).comp_left
      (g := fun v : Space => basisVector i ⨯₃ v) (by simp)
  have hsum : HasCompactSupport
      (∑ i : Fin 3, fun x : Space =>
        basisVector i ⨯₃ fderiv ℝ w x (basisVector i)) := by
    simpa using HasCompactSupport.finset_sum
      (s := Finset.univ) (f := fun i : Fin 3 => fun x : Space =>
        basisVector i ⨯₃ fderiv ℝ w x (basisVector i))
      (fun i _ => hterm i)
  change HasCompactSupport (fun x : Space => ∑ i : Fin 3,
    basisVector i ⨯₃ fderiv ℝ w x (basisVector i))
  exact hsum

/-- Native `div curl = 0` makes every positive-radius cutoff solenoidal. -/
theorem solenoidalCutoffField_divergenceFree
    (R : ℝ) (A : Space → Space) (hA : ContDiff ℝ ∞ A) (x : Space) :
    staticDivergence (solenoidalCutoffField R A) x = 0 := by
  unfold solenoidalCutoffField
  exact staticDivergence_staticCurl_eq_zero
    (fun y => scaledCutoff R y • A y) x
    (((scaledCutoff_contDiff R).smul hA).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))

/-- The curl cutoff as the exact compact test carrier consumed by the local
pressure-free Leray evolution identity. -/
def solenoidalCutoffTest
    (R : ℝ) (hR : 0 < R) (A : Space → Space) (hA : ContDiff ℝ ∞ A) :
    CompactSolenoidalTest :=
  CompactSolenoidalTest.ofNative
    (solenoidalCutoffField R A)
    (solenoidalCutoffField_contDiff R A hA)
    (solenoidalCutoffField_hasCompactSupport hR A)
    (solenoidalCutoffField_divergenceFree R A hA)

/-- **Exact curl-cutoff decomposition.**  This isolates the sole first-order
cutoff correction from the desired solenoidal test `curl A`. -/
theorem solenoidalCutoffField_eq
    (R : ℝ) (A : Space → Space) (hA : ContDiff ℝ ∞ A) (x : Space) :
    solenoidalCutoffField R A x =
      staticGradient (scaledCutoff R) x ⨯₃ A x +
        scaledCutoff R x • staticCurl A x := by
  unfold solenoidalCutoffField
  exact staticCurl_smul (scaledCutoff R) A x
    ((scaledCutoff_contDiff R).differentiable (by norm_num)).differentiableAt
    (hA.differentiable (by norm_num)).differentiableAt

/-- The derivative in the exact correction has an explicit `R^-1` bound in
each native coordinate.  The constant depends only on the fixed standard
bump, never on `R`, the potential, or the solution. -/
theorem exists_scaledCutoff_gradient_component_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space, ∀ i : Fin 3,
      |staticGradient (scaledCutoff R) x i| ≤ R⁻¹ * M := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_opNorm_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
  refine ⟨M, hM0, ?_⟩
  intro R hR x i
  have h := abs_fderiv_scaled_le standardBump standardBump.contDiff hM hR x
    (basisVector i)
  have hb : ‖(basisVector i : Space)‖ = 1 := by
    change ‖(Pi.single i (1 : ℝ) : Space)‖ = 1
    rw [Pi.norm_single, norm_one]
  rw [hb, mul_one] at h
  change |fderiv ℝ (fun y => standardBump (R⁻¹ • y)) x (basisVector i)| ≤
    R⁻¹ * M
  exact h

/-- The explicit derivative rate implies that the cutoff gradient vanishes at
every fixed spatial point. -/
theorem scaledCutoff_staticGradient_tendsto_zero (x : Space) :
    Filter.Tendsto (fun R : ℝ => staticGradient (scaledCutoff R) x)
      Filter.atTop (nhds 0) := by
  obtain ⟨M, _, hM⟩ := exists_scaledCutoff_gradient_component_bound
  rw [tendsto_pi_nhds]
  intro i
  apply squeeze_zero_norm' (a := fun R : ℝ => R⁻¹ * M)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.norm_eq_abs]
    exact hM hR x i
  · simpa using tendsto_inv_atTop_zero.mul_const M

/-- **Actual pointwise approximation.**  The compact solenoidal fields
`curl (chi_R A)` converge to `curl A` on every fixed point.  The proof uses
the exact product decomposition, the checked `R^-1` gradient estimate, and
eventual pointwise equality `chi_R(x)=1`. -/
theorem solenoidalCutoffField_tendsto
    (A : Space → Space) (hA : ContDiff ℝ ∞ A) (x : Space) :
    Filter.Tendsto (fun R : ℝ => solenoidalCutoffField R A x)
      Filter.atTop (nhds (staticCurl A x)) := by
  have hgrad := scaledCutoff_staticGradient_tendsto_zero x
  have hcross : Filter.Tendsto
      (fun R : ℝ => staticGradient (scaledCutoff R) x ⨯₃ A x)
      Filter.atTop (nhds 0) := by
    have hc : Continuous (fun v : Space => -(A x ⨯₃ v)) :=
      (crossProduct (A x)).toContinuousLinearMap.continuous.neg
    have hc' : Continuous (fun v : Space => v ⨯₃ A x) := by
      simpa only [cross_anticomm] using hc
    have hz : (0 : Space) ⨯₃ A x = 0 := by
      rw [← cross_anticomm]
      simp
    simpa only [Function.comp_def, hz] using hc'.continuousAt.tendsto.comp hgrad
  have hscaled : Filter.Tendsto
      (fun R : ℝ => scaledCutoff R x • staticCurl A x)
      Filter.atTop (nhds (staticCurl A x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [scaledCutoff_eventually_one x] with R hR
    simp [hR]
  have heq : (fun R : ℝ =>
      staticGradient (scaledCutoff R) x ⨯₃ A x +
        scaledCutoff R x • staticCurl A x) =ᶠ[Filter.atTop]
      (fun R : ℝ => solenoidalCutoffField R A x) := by
    filter_upwards with R
    exact (solenoidalCutoffField_eq R A hA x).symm
  simpa using (hcross.add hscaled).congr' heq

/-- A backward heat vector potential.  Its curl is a smooth solenoidal
derivative-Gaussian test, while the curl cutoff above supplies compact tests
accepted by the pressure-free weak evolution identity. -/
def backwardHeatPotential
    (κ τ : ℝ) (x₀ a : Space) : Space → Space :=
  fun y => heatKernel κ τ (x₀ - y) • a

theorem backwardHeatPotential_contDiff
    (κ τ : ℝ) (x₀ a : Space) :
    ContDiff ℝ ∞ (backwardHeatPotential κ τ x₀ a) := by
  exact (heatKernel_translate_contDiff κ τ x₀).smul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => a))

/-- The concrete compact, divergence-free backward heat test. -/
def compactBackwardHeatCurlTest
    (R : ℝ) (hR : 0 < R) (κ τ : ℝ) (x₀ a : Space) :
    CompactSolenoidalTest :=
  solenoidalCutoffTest R hR (backwardHeatPotential κ τ x₀ a)
    (backwardHeatPotential_contDiff κ τ x₀ a)

/-- **Actual consumer.**  Every local trajectory used by the whole-space
continuation construction obeys the pressure-free evolution identity against
the concrete divergence-preserving compact backward heat test. -/
theorem solvesBefore_compactBackwardHeatCurlEvolution
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {R : ℝ} (hR : 0 < R) (κ τ : ℝ) (x₀ a₀ : Space)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    testedMomentum (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u b -
        testedMomentum (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u a =
      ∫ t in a..b,
        lerayWeakRhs ν (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u t :=
  solvesBefore_lerayWeakEvolution_timeIntegrated hT hsol
    (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) ha0 hab hbT

end Navier.Analysis.WholeSpaceSolenoidalHeatApproximation

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatApproximation.solenoidalCutoffField_eq
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatApproximation.exists_scaledCutoff_gradient_component_bound
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatApproximation.solenoidalCutoffField_tendsto
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatApproximation.solvesBefore_compactBackwardHeatCurlEvolution
