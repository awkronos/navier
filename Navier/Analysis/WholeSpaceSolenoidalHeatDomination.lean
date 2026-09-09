import Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
import Navier.Analysis.EnergyNormBridge

/-!
# Uniform derivative rates for whole-space solenoidal heat cutoffs

The compact solenoidal test is `curl (chi_R A)`.  Its first two derivatives
therefore contain derivatives of the scalar multiplier through order three.
The first- and second-order scaling estimates already live in `ScaledCutoff`.
This file proves the missing third-order estimate and packages all three
rates with the actual backward-heat weak-evolution consumer.

These are uniform analytic bounds on the concrete cutoff family.  They do not
assume a Duhamel representation or a bound on the solution.  Completing the
limit still requires product-rule assembly with the Gaussian potential and
an integrable space-time envelope for those Gaussian derivative factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Interval BigOperators Matrix
open MeasureTheory Set

namespace Navier.Analysis.WholeSpaceSolenoidalHeatDomination

open Navier
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.EnergyNormBridge

/-- Third directional derivative of a scalar field, with direction order
`v`, then `w`, then `q`. -/
def thirdDirectional
    (χ : Space → ℝ) (v w q x : Space) : ℝ :=
  fderiv ℝ (fun r => fderiv ℝ (fun z => fderiv ℝ χ z v) r w) x q

/-- Exact third-derivative scaling.  Each spatial derivative of
`χ(R⁻¹ x)` contributes one factor `R⁻¹`. -/
theorem thirdDirectional_scaled
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (R : ℝ) (x v w q : Space) :
    thirdDirectional (fun y => χ (R⁻¹ • y)) v w q x =
      R⁻¹ * (R⁻¹ * (R⁻¹ * thirdDirectional χ v w q (R⁻¹ • x))) := by
  have hD2 : ContDiff ℝ ∞
      (fun y => fderiv ℝ (fun z => fderiv ℝ χ z v) y w) :=
    contDiff_fderiv_apply (contDiff_fderiv_apply hχ v) w
  have hshape :
      (fun r => fderiv ℝ (fun z => fderiv ℝ
        (fun a => χ (R⁻¹ • a)) z v) r w) =
      (fun r => R⁻¹ * (R⁻¹ *
        (fun z => fderiv ℝ (fun a => fderiv ℝ χ a v) z w) (R⁻¹ • r))) := by
    funext r
    exact fderiv_fderiv_scaled_apply χ hχ R r v w
  unfold thirdDirectional
  rw [hshape]
  have hscaled : DifferentiableAt ℝ
      (fun r : Space =>
        (fun z => fderiv ℝ (fun a => fderiv ℝ χ a v) z w) (R⁻¹ • r)) x :=
    ((contDiff_scaled _ hD2 R).differentiable (by norm_num)).differentiableAt
  have hinner : DifferentiableAt ℝ
      (fun r : Space => R⁻¹ *
        (fun z => fderiv ℝ (fun a => fderiv ℝ χ a v) z w) (R⁻¹ • r)) x :=
    hscaled.const_mul R⁻¹
  rw [fderiv_const_mul hinner R⁻¹]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hscaled R⁻¹]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_scaled_apply _ hD2 R x q]

/-- Every fixed third directional derivative of a smooth compactly supported
scalar has a finite global bound. -/
theorem exists_thirdDirectional_bound
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) (v w q : Space) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Space,
      |thirdDirectional χ v w q x| ≤ M := by
  have hD3 : ContDiff ℝ ∞ (fun x => thirdDirectional χ v w q x) :=
    contDiff_fderiv_apply
      (contDiff_fderiv_apply (contDiff_fderiv_apply hχ v) w) q
  have hsupp3 : HasCompactSupport (fun x => thirdDirectional χ v w q x) :=
    hasCompactSupport_fderiv_apply
      (hasCompactSupport_fderiv_apply
        (hasCompactSupport_fderiv_apply hsupp v) w) q
  obtain ⟨x₀, hx₀⟩ := hD3.continuous.abs.exists_forall_ge_of_hasCompactSupport
    hsupp3.abs
  exact ⟨|thirdDirectional χ v w q x₀|, abs_nonneg _, hx₀⟩

/-- **Third-order cutoff rate.**  The third derivative needed by the
Laplacian of `curl (χ_R A)` is `O(R⁻³)`. -/
theorem abs_thirdDirectional_scaled_le
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {v w q : Space} {M : ℝ}
    (hM : ∀ y : Space, |thirdDirectional χ v w q y| ≤ M)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    |thirdDirectional (fun y => χ (R⁻¹ • y)) v w q x| ≤
      R⁻¹ * R⁻¹ * R⁻¹ * M := by
  rw [thirdDirectional_scaled χ hχ R x v w q,
    abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos hR]
  have hRnn : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
  calc
    R⁻¹ * (R⁻¹ * (R⁻¹ * |thirdDirectional χ v w q (R⁻¹ • x)|)) ≤
        R⁻¹ * (R⁻¹ * (R⁻¹ * M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hM _) hRnn) hRnn) hRnn
    _ = R⁻¹ * R⁻¹ * R⁻¹ * M := by ring

/-- The concrete standard cutoff has simultaneous first-, second-, and
third-order coordinate rates.  These are precisely the cutoff factors in the
first and second derivatives of the curl-generated test. -/
theorem standardCutoff_coordinate_derivative_rates :
    (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space, ∀ i : Fin 3,
      |fderiv ℝ (scaledCutoff R) x (basisVector i)| ≤ R⁻¹ * M₁) ∧
    (∀ i j : Fin 3, ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |fderiv ℝ (fun z => fderiv ℝ (scaledCutoff R) z (basisVector i)) x
        (basisVector j)| ≤ R⁻¹ * R⁻¹ * M₂) ∧
    (∀ i j k : Fin 3, ∃ M₃ : ℝ, 0 ≤ M₃ ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Space,
      |thirdDirectional (scaledCutoff R)
        (basisVector i) (basisVector j) (basisVector k) x| ≤
          R⁻¹ * R⁻¹ * R⁻¹ * M₃) := by
  constructor
  · obtain ⟨M, hM0, hM⟩ := exists_fderiv_opNorm_bound
      standardBump standardBump.contDiff standardBump.hasCompactSupport
    refine ⟨M, hM0, ?_⟩
    intro R hR x i
    have h := abs_fderiv_scaled_le standardBump standardBump.contDiff hM hR x
      (basisVector i)
    have hb : ‖(basisVector i : Space)‖ = 1 := by
      change ‖(Pi.single i (1 : ℝ) : Space)‖ = 1
      rw [Pi.norm_single, norm_one]
    rw [hb, mul_one] at h
    change |fderiv ℝ (fun y => standardBump (R⁻¹ • y)) x
      (basisVector i)| ≤ R⁻¹ * M
    exact h
  constructor
  · intro i j
    obtain ⟨M, hM0, hM⟩ := exists_fderiv_fderiv_bound
      standardBump standardBump.contDiff standardBump.hasCompactSupport
      (basisVector i) (basisVector j)
    refine ⟨M, hM0, ?_⟩
    intro R hR x
    change |fderiv ℝ (fun z => fderiv ℝ
      (fun y => standardBump (R⁻¹ • y)) z (basisVector i)) x
        (basisVector j)| ≤ R⁻¹ * R⁻¹ * M
    exact abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff hM hR x
  · intro i j k
    obtain ⟨M, hM0, hM⟩ := exists_thirdDirectional_bound
      standardBump standardBump.contDiff standardBump.hasCompactSupport
      (basisVector i) (basisVector j) (basisVector k)
    refine ⟨M, hM0, ?_⟩
    intro R hR x
    change |thirdDirectional (fun y => standardBump (R⁻¹ • y))
      (basisVector i) (basisVector j) (basisVector k) x| ≤ _
    exact abs_thirdDirectional_scaled_le standardBump standardBump.contDiff
      hM hR x

/-! ### Energy-only domination of the first Gaussian cutoff remainder -/

/-- A positive-time heat kernel translate is bounded by its value at the
Gaussian peak. -/
theorem heatKernel_translate_le_peak
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ y : Space) :
    heatKernel κ τ (x₀ - y) ≤ (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) := by
  have hbase : 0 < 4 * Real.pi * κ * τ := by positivity
  have hexp : Real.exp
      (-(4 * κ * τ)⁻¹ * ∑ i : Fin 3, (x₀ - y) i ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (inv_nonneg.mpr (by positivity)))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  unfold heatKernel
  calc
    (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(4 * κ * τ)⁻¹ * ∑ i : Fin 3, (x₀ - y) i ^ 2) ≤
        (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hbase.le _)
    _ = (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) := mul_one _

/-- **Quantitative finite-energy Gaussian cutoff domination.**  The first
cutoff derivative paired with the quadratic velocity term is bounded by
`R⁻¹` times the inherited finite energy.  The constant is explicit up to the
fixed standard-bump derivative bound and is independent of the velocity
field and the spatial center. -/
theorem exists_gaussianCutoffConvectionTail_abs_le_energy
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    (x₀ : Space) (v : Space → Space) (hv : Continuous v)
    (hint : Integrable (fun y : Space => ‖v y‖ ^ 2)) (j : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R →
      |∫ y : Space, fderiv ℝ (scaledCutoff R) y (v y) *
          (heatKernel κ τ (x₀ - y) * v y j)| ≤
        R⁻¹ * M * (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) *
          (∫ y : Space, ‖v y‖ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_opNorm_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
  refine ⟨M, hM0, ?_⟩
  intro R hR
  let K : ℝ := (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2)
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hupper : Integrable (fun y : Space => R⁻¹ * M * K * ‖v y‖ ^ 2) :=
    hint.const_mul (R⁻¹ * M * K)
  have hlower : Integrable (fun y : Space =>
      ‖fderiv ℝ (scaledCutoff R) y (v y) *
        (heatKernel κ τ (x₀ - y) * v y j)‖) := by
    have hD : Continuous (fun y : Space =>
        fderiv ℝ (scaledCutoff R) y (v y)) :=
      ((scaledCutoff_contDiff R).continuous_fderiv (by norm_num)).clm_apply hv
    have hG : Continuous (fun y : Space => heatKernel κ τ (x₀ - y)) :=
      (heatKernel_continuous κ τ).comp (continuous_const.sub continuous_id)
    have hc : Continuous (fun y : Space =>
        ‖fderiv ℝ (scaledCutoff R) y (v y) *
          (heatKernel κ τ (x₀ - y) * v y j)‖) :=
      (hD.mul (hG.mul ((continuous_apply j).comp hv))).norm
    have hgradSupp : HasCompactSupport (fun y : Space =>
        fderiv ℝ (scaledCutoff R) y (v y)) := by
      refine ((scaledCutoff_hasCompactSupport hR).fderiv ℝ).mono ?_
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hzero
      exact hy (by rw [hzero]; simp)
    exact hc.integrable_of_hasCompactSupport
      ((hgradSupp.mul_right
        (f' := fun y : Space => heatKernel κ τ (x₀ - y) * v y j)).norm)
  calc
    |∫ y : Space, fderiv ℝ (scaledCutoff R) y (v y) *
          (heatKernel κ τ (x₀ - y) * v y j)| ≤
        ∫ y : Space, ‖fderiv ℝ (scaledCutoff R) y (v y) *
          (heatKernel κ τ (x₀ - y) * v y j)‖ := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y : Space => fderiv ℝ (scaledCutoff R) y (v y) *
          (heatKernel κ τ (x₀ - y) * v y j))
    _ ≤ ∫ y : Space, R⁻¹ * M * K * ‖v y‖ ^ 2 := by
      apply integral_mono hlower hupper
      intro y
      have hd := abs_fderiv_scaled_le standardBump standardBump.contDiff
        hM hR y (v y)
      have hG0 := heatKernel_nonneg hκ hτ (x₀ - y)
      have hG := heatKernel_translate_le_peak hκ hτ x₀ y
      have hj : |v y j| ≤ ‖v y‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (v y) j
      dsimp only
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hG0]
      calc
        |fderiv ℝ (scaledCutoff R) y (v y)| *
            (heatKernel κ τ (x₀ - y) * |v y j|) ≤
          (R⁻¹ * M * ‖v y‖) * (K * ‖v y‖) :=
        mul_le_mul hd (mul_le_mul hG hj (abs_nonneg _) hK0)
          (mul_nonneg hG0 (abs_nonneg _))
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr hR.le) hM0) (norm_nonneg _))
        _ = R⁻¹ * M * K * ‖v y‖ ^ 2 := by ring
    _ = R⁻¹ * M * K * (∫ y : Space, ‖v y‖ ^ 2) := by
      rw [integral_const_mul]

/-- On the exact `SolvesBefore` carrier, the preceding estimate is uniform in
the time slice: the inherited energy is bounded by the official kinetic
energy, which the continuation record bounds by its initial value. -/
theorem solvesBefore_gaussianCutoffConvectionTail_abs_le_initialEnergy
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) (j : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {R : ℝ}, 0 < R →
      |∫ y : Space, fderiv ℝ (scaledCutoff R) y (u t y) *
          (heatKernel κ τ (x₀ - y) * u t y j)| ≤
        R⁻¹ * M * (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) *
          kineticEnergy u 0 := by
  have hu : ContDiff ℝ ∞ (u t) :=
    contDiff_iff_contDiffAt.mpr fun x =>
      contDiffAt_spatial_slice_before hsol.classical.1 ht0 htT x
  obtain ⟨M, hM0, hM⟩ := exists_gaussianCutoffConvectionTail_abs_le_energy
    hκ hτ x₀ (u t) hu.continuous (hsol.finite_energy t ht0 htT) j
  refine ⟨M, hM0, ?_⟩
  intro R hR
  have hsup : (∫ y : Space, ‖u t y‖ ^ 2) ≤ kineticEnergy u t := by
    exact supKineticEnergy_le_kineticEnergy u t hu.continuous.aestronglyMeasurable
      (hsol.finite_energy t ht0 htT)
  have hcoef : 0 ≤ R⁻¹ * M * (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2) := by
    positivity
  exact (hM hR).trans <| (mul_le_mul_of_nonneg_left hsup hcoef).trans
    (mul_le_mul_of_nonneg_left (hsol.energy_le_initial t ht0 htT) hcoef)

/-- The derivative rates are packaged with the exact weak evolution of the
same concrete compact solenoidal backward-heat test.  This records the actual
consumer rather than leaving the new estimates disconnected from the
whole-space continuation carrier. -/
theorem solvesBefore_heatCurlEvolution_with_cutoffDerivativeRates
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {R : ℝ} (hR : 0 < R) (κ τ : ℝ) (x₀ a₀ : Space)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (testedMomentum (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u b -
        testedMomentum (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u a =
      ∫ t in a..b,
        lerayWeakRhs ν (compactBackwardHeatCurlTest R hR κ τ x₀ a₀) u t) ∧
      (∀ i j k : Fin 3, ∃ M₃ : ℝ, 0 ≤ M₃ ∧ ∀ {S : ℝ}, 0 < S → ∀ x : Space,
        |thirdDirectional (scaledCutoff S)
          (basisVector i) (basisVector j) (basisVector k) x| ≤
            S⁻¹ * S⁻¹ * S⁻¹ * M₃) := by
  refine ⟨solvesBefore_compactBackwardHeatCurlEvolution hT hsol hR κ τ x₀ a₀
    ha0 hab hbT, ?_⟩
  exact standardCutoff_coordinate_derivative_rates.2.2

end Navier.Analysis.WholeSpaceSolenoidalHeatDomination

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.thirdDirectional_scaled
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.abs_thirdDirectional_scaled_le
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.standardCutoff_coordinate_derivative_rates
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.exists_gaussianCutoffConvectionTail_abs_le_energy
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.solvesBefore_gaussianCutoffConvectionTail_abs_le_initialEnergy
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatDomination.solvesBefore_heatCurlEvolution_with_cutoffDerivativeRates
