import Navier.Analysis.LeiLinPositiveRestartGalerkin

/-!
# Positive-restart Volterra bootstrap boundary

This module isolates the exact analytic boundary in the attempted
positive-time half-generator bootstrap.  The inverse-square-root Volterra
kernel and an `L¹` half-generator moment are separately integrable, but their
endpoint product need not be.  Thus the weighted-integrability premise of the
literal Duhamel half-moment estimate cannot be recovered from the completed
critical path's current `L¹` information alone.

On the positive side, the truncated kernel is packaged as an actual
convolution.  Its total mass is exactly `2 * sqrt δ`, so a literal pointwise
split-Volterra inequality immediately yields the averaged Lei--Lin recurrence
with coefficient `4 * R / sqrt ν * sqrt δ`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinPositiveRestartBootstrap

open Filter
open MeasureTheory
open Set
open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinTimeMixed
open Navier.Analysis.LeiLinPositiveRestart
open Navier.Analysis.LeiLinPositiveRestartGalerkin

/-- The inverse-square-root kernel cut off to a restart interval. -/
def truncatedInverseSqrtTime (δ : ℝ) : ℝ → ℝ :=
  (Ioc 0 δ).indicator inverseSqrtTime

/-- Extension by zero of a trailing-interval moment. -/
def trailingExtension (a b : ℝ) (M : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc a b).indicator M

/-- The literal restart kernel acting on the zero-extended trailing moment. -/
def truncatedVolterraConvolution (a b : ℝ) (M : ℝ → ℝ) : ℝ → ℝ :=
  convolution
    (truncatedInverseSqrtTime (b - a))
    (trailingExtension a b M)
    (ContinuousLinearMap.mul ℝ ℝ) volume

/-- Explicit half-generator majorant for the free heat evolution restarted at
time `a`. -/
def restartFreeHalfMomentMajorant (ν a : ℝ)
    (u : WeightedLatticeBanach) (t : ℝ) : ℝ :=
  (Real.sqrt ν)⁻¹ * ‖u‖ * inverseSqrtTime (t - a)

theorem heatHalfGeneratorMoment_weightedHeatFlow_le_restartFree
    (ν : ℝ) (hν : 0 < ν) (a t : ℝ) (hat : a < t)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatHalfGeneratorMoment
        (weightedHeatFlow ν (t - a) hν.le (sub_nonneg.mpr hat.le) u) ≤
      restartFreeHalfMomentMajorant ν a u t := by
  calc
    heatHalfGeneratorMoment
        (weightedHeatFlow ν (t - a) hν.le (sub_nonneg.mpr hat.le) u) ≤
        (Real.sqrt (ν * (t - a)))⁻¹ * ‖u‖ :=
      heatHalfGeneratorMoment_weightedHeatFlow_le
        ν (t - a) hν (sub_pos.mpr hat) u hu
    _ = restartFreeHalfMomentMajorant ν a u t := by
      rw [outputHeatGain_eq_inverseSqrtTime ν (t - a) hν (sub_pos.mpr hat)]
      unfold restartFreeHalfMomentMajorant
      ring

theorem intervalIntegrable_restartFreeHalfMomentMajorant
    (ν : ℝ) (_hν : 0 < ν) (a δ : ℝ)
    (u : WeightedLatticeBanach) :
    IntervalIntegrable (restartFreeHalfMomentMajorant ν a u)
      volume a (a + δ) := by
  change IntervalIntegrable
    (fun t => (Real.sqrt ν)⁻¹ * ‖u‖ * inverseSqrtTime (t - a))
    volume a (a + δ)
  have hshift := (inverseSqrtTime_intervalIntegrable δ).comp_sub_right a
  have hscaled := hshift.const_mul ((Real.sqrt ν)⁻¹ * ‖u‖)
  rw [add_comm a δ]
  simpa only [zero_add] using hscaled

theorem integral_restartFreeHalfMomentMajorant
    (ν : ℝ) (hν : 0 < ν) (a δ : ℝ) (hδ : 0 ≤ δ)
    (u : WeightedLatticeBanach) :
    (∫ t in a..(a + δ), restartFreeHalfMomentMajorant ν a u t) =
      2 * Real.sqrt δ / Real.sqrt ν * ‖u‖ := by
  unfold restartFreeHalfMomentMajorant
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right]
  simp only [add_sub_cancel_left, sub_self]
  rw [integral_inverseSqrtTime_zero δ hδ]
  have hsqrt : Real.sqrt ν ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hν)
  field_simp

theorem integrable_truncatedInverseSqrtTime {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (truncatedInverseSqrtTime δ) volume := by
  apply IntegrableOn.integrable_indicator
  · have h := intervalIntegrable_iff.mp
      (inverseSqrtTime_intervalIntegrable δ)
    simpa [uIoc_of_le hδ] using h
  · exact measurableSet_Ioc

theorem integral_truncatedInverseSqrtTime {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ r : ℝ, truncatedInverseSqrtTime δ r) = 2 * Real.sqrt δ := by
  rw [truncatedInverseSqrtTime, integral_indicator measurableSet_Ioc]
  simpa [intervalIntegral.integral_of_le hδ] using
    (integral_inverseSqrtTime_zero δ hδ)

theorem integrable_trailingExtension {a b : ℝ} {M : ℝ → ℝ}
    (hab : a ≤ b) (hM : IntervalIntegrable M volume a b) :
    Integrable (trailingExtension a b M) volume := by
  apply IntegrableOn.integrable_indicator
  · have h := intervalIntegrable_iff.mp hM
    simpa [uIoc_of_le hab] using h
  · exact measurableSet_Ioc

theorem integral_trailingExtension {a b : ℝ} {M : ℝ → ℝ}
    (hab : a ≤ b) :
    (∫ s : ℝ, trailingExtension a b M s) = ∫ s in a..b, M s := by
  rw [trailingExtension, integral_indicator measurableSet_Ioc]
  simp only [intervalIntegral.integral_of_le hab]

/-- Exact total mass of the literal truncated Volterra convolution. -/
theorem integral_truncatedVolterraConvolution
    {a b : ℝ} {M : ℝ → ℝ} (hab : a ≤ b)
    (hM : IntervalIntegrable M volume a b) :
    (∫ t : ℝ, truncatedVolterraConvolution a b M t) =
      2 * Real.sqrt (b - a) * (∫ s in a..b, M s) := by
  unfold truncatedVolterraConvolution
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_truncatedInverseSqrtTime (sub_nonneg.mpr hab))
    (integrable_trailingExtension hab hM)]
  rw [integral_truncatedInverseSqrtTime (sub_nonneg.mpr hab),
    integral_trailingExtension hab]
  rfl

theorem integrable_truncatedVolterraConvolution
    {a b : ℝ} {M : ℝ → ℝ} (hab : a ≤ b)
    (hM : IntervalIntegrable M volume a b) :
    Integrable (truncatedVolterraConvolution a b M) volume := by
  unfold truncatedVolterraConvolution
  exact (integrable_truncatedInverseSqrtTime (sub_nonneg.mpr hab)).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_trailingExtension hab hM)

theorem truncatedVolterraConvolution_nonneg
    {a b : ℝ} {M : ℝ → ℝ}
    (hM0 : ∀ s ∈ Ioc a b, 0 ≤ M s) (t : ℝ) :
    0 ≤ truncatedVolterraConvolution a b M t := by
  unfold truncatedVolterraConvolution convolution
  apply integral_nonneg
  intro r
  have hk : 0 ≤ truncatedInverseSqrtTime (b - a) r := by
    apply indicator_nonneg
    intro x hx
    unfold inverseSqrtTime
    exact Real.rpow_nonneg hx.1.le _
  have hm : 0 ≤ trailingExtension a b M (t - r) := by
    exact indicator_nonneg hM0 (t - r)
  simpa using mul_nonneg hk hm

/-- Restricting the nonnegative literal convolution to the restart interval
costs no more than its exact whole-line mass. -/
theorem integral_truncatedVolterraConvolution_interval_le
    {a b : ℝ} {M : ℝ → ℝ} (hab : a ≤ b)
    (hM : IntervalIntegrable M volume a b)
    (hM0 : ∀ s ∈ Ioc a b, 0 ≤ M s) :
    (∫ t in a..b, truncatedVolterraConvolution a b M t) ≤
      2 * Real.sqrt (b - a) * (∫ s in a..b, M s) := by
  rw [intervalIntegral.integral_of_le hab]
  calc
    (∫ t in Ioc a b, truncatedVolterraConvolution a b M t) ≤
        ∫ t : ℝ, truncatedVolterraConvolution a b M t := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (truncatedVolterraConvolution_nonneg hM0))
        (integrable_truncatedVolterraConvolution hab hM)
    _ = 2 * Real.sqrt (b - a) * (∫ s in a..b, M s) :=
      integral_truncatedVolterraConvolution hab hM

/-- Integrating a literal pointwise Volterra inequality and using the exact
kernel mass.  This is the reusable Fubini/Young step behind the averaged
Lei--Lin recurrence. -/
theorem averagedVolterra_of_literalConvolution
    {a b c : ℝ} {M F : ℝ → ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hM : IntervalIntegrable M volume a b)
    (hF : IntervalIntegrable F volume a b)
    (hM0 : ∀ s ∈ Ioc a b, 0 ≤ M s)
    (hpoint : ∀ t ∈ Icc a b,
      M t ≤ F t + c * truncatedVolterraConvolution a b M t) :
    (∫ t in a..b, M t) ≤
      (∫ t in a..b, F t) +
        c * (2 * Real.sqrt (b - a) * (∫ s in a..b, M s)) := by
  have hVint : IntervalIntegrable (truncatedVolterraConvolution a b M)
      volume a b :=
    (integrable_truncatedVolterraConvolution hab hM).intervalIntegrable
  have hcVint : IntervalIntegrable
      (fun t => c * truncatedVolterraConvolution a b M t) volume a b :=
    hVint.const_mul c
  have hmono : (∫ t in a..b, M t) ≤
      ∫ t in a..b, F t + c * truncatedVolterraConvolution a b M t :=
    intervalIntegral.integral_mono_on hab hM (hF.add hcVint) hpoint
  rw [intervalIntegral.integral_add hF hcVint,
    intervalIntegral.integral_const_mul] at hmono
  calc
    (∫ t in a..b, M t) ≤
        (∫ t in a..b, F t) +
          c * (∫ t in a..b, truncatedVolterraConvolution a b M t) := hmono
    _ ≤ (∫ t in a..b, F t) +
          c * (2 * Real.sqrt (b - a) * (∫ s in a..b, M s)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          (integral_truncatedVolterraConvolution_interval_le hab hM hM0) hc) _

/-- The literal split-Duhamel coefficient specializes to the exact averaged
coefficient used by the positive-restart terminal consumer. -/
theorem averaged_splitVolterra_of_literalConvolution
    {ν R T δ : ℝ} {M F : ℝ → ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (_hδT : δ ≤ T)
    (hM : IntervalIntegrable M volume (T - δ) T)
    (hF : IntervalIntegrable F volume (T - δ) T)
    (hM0 : ∀ s ∈ Ioc (T - δ) T, 0 ≤ M s)
    (hpoint : ∀ t ∈ Icc (T - δ) T,
      M t ≤ F t + (2 * (Real.sqrt ν)⁻¹ * R) *
        truncatedVolterraConvolution (T - δ) T M t) :
    (∫ t in (T - δ)..T, M t) ≤
      (∫ t in (T - δ)..T, F t) +
        (4 * R / Real.sqrt ν) * Real.sqrt δ *
          (∫ s in (T - δ)..T, M s) := by
  have hab : T - δ ≤ T := sub_le_self T hδ
  have hc : 0 ≤ 2 * (Real.sqrt ν)⁻¹ * R := by positivity
  have h := averagedVolterra_of_literalConvolution hab hc hM hF hM0 hpoint
  have hsub : T - (T - δ) = δ := by ring
  have hsqrt : Real.sqrt ν ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hν)
  calc
    (∫ t in (T - δ)..T, M t) ≤
        (∫ t in (T - δ)..T, F t) +
          (2 * (Real.sqrt ν)⁻¹ * R) *
            (2 * Real.sqrt (T - (T - δ)) *
              (∫ s in (T - δ)..T, M s)) := h
    _ = (∫ t in (T - δ)..T, F t) +
        (4 * R / Real.sqrt ν) * Real.sqrt δ *
          (∫ s in (T - δ)..T, M s) := by
      rw [hsub]
      field_simp
      ring

/-- **Critical endpoint obstruction.**  Arbitrarily small Volterra
coefficients do not turn an `L¹` moment into the endpoint-weighted
integrability required by the literal Duhamel half-generator estimate. -/
theorem exists_smallCoefficient_integrableMoment_with_nonintegrableKernelProduct :
    ∃ (c : ℝ) (M : ℝ → ℝ),
      0 < c ∧ c < 1 ∧
      IntervalIntegrable M volume 0 1 ∧
      ¬ IntervalIntegrable
        (fun τ => c * inverseSqrtTime τ * M τ) volume 0 1 := by
  refine ⟨(1 / 2 : ℝ), inverseSqrtTime, by norm_num, by norm_num,
    inverseSqrtTime_L1_product_endpoint_obstruction.1, ?_⟩
  intro hscaled
  have hrescaled := hscaled.const_mul (2 : ℝ)
  apply inverseSqrtTime_L1_product_endpoint_obstruction.2
  convert hrescaled using 1
  funext τ
  ring

/-- **Positive-restart consumer with the averaged recurrence discharged.**

The free term is the explicit restarted heat majorant.  The literal pointwise
split-Volterra inequality is integrated by
`averaged_splitVolterra_of_literalConvolution`, so no separate averaged
recurrence hypothesis remains.  The graph-domain and moment-integrability
hypotheses remain explicit: the endpoint obstruction above proves they cannot
be manufactured by the currently available critical `L¹` data alone. -/
theorem positiveRestart_graph_X2_and_terminal_X1_of_literalSplitVolterra
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T δ A : ℝ} (hR : 0 ≤ R)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδT : δ ≤ T)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmild : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T),
      u s = criticalMildImage ν hν u₀ u hu s hs.1)
    (hhalf : ∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (hmoment : IntervalIntegrable (fun s => heatHalfGeneratorMoment (u s))
      volume (T - δ) T)
    (hintX1 : IntervalIntegrable
      (fun s => normX1 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T)
    (hmassX1 : (∫ s in (T - δ)..T,
      normX1 latticeModeSize (weightedAmplitude (u s))) ≤ A)
    (hsmall : (4 * R / Real.sqrt ν) * Real.sqrt δ < 1)
    (hpoint : ∀ t ∈ Icc (T - δ) T,
      heatHalfGeneratorMoment (u t) ≤
        restartFreeHalfMomentMajorant ν (T - δ) (u (T - δ)) t +
          (2 * (Real.sqrt ν)⁻¹ * R) *
            truncatedVolterraConvolution (T - δ) T
              (fun s => heatHalfGeneratorMoment (u s)) t) :
    (∀ r (hr : r ∈ Icc (0 : ℝ) δ),
      criticalMildRestartImage ν hν u hu (T - δ) r hr.1 =
        u (T - δ + r)) ∧
    (∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) ∧
    IntervalIntegrable
      (fun s => normX2 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T ∧
    (∫ s in (T - δ)..T,
      normX2 latticeModeSize (weightedAmplitude (u s))) ≤
        (2 * Real.sqrt δ / Real.sqrt ν * ‖u (T - δ)‖) /
          (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) ∧
    normX1 latticeModeSize (weightedAmplitude (u T)) ≤
      (A + (Real.sqrt ν *
          ((2 * Real.sqrt δ / Real.sqrt ν * ‖u (T - δ)‖) /
            (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ))) *
          Real.sqrt δ) / δ +
        (2 * R ^ 2 / Real.sqrt ν) * Real.sqrt δ := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hFint0 := intervalIntegrable_restartFreeHalfMomentMajorant
    ν hν (T - δ) δ (u (T - δ))
  have hFint : IntervalIntegrable
      (restartFreeHalfMomentMajorant ν (T - δ) (u (T - δ)))
      volume (T - δ) T := by
    simpa only [sub_add_cancel] using hFint0
  have hFmass0 := integral_restartFreeHalfMomentMajorant
    ν hν (T - δ) δ hδ0 (u (T - δ))
  have hFmass :
      (∫ t in (T - δ)..T,
        restartFreeHalfMomentMajorant ν (T - δ) (u (T - δ)) t) =
        2 * Real.sqrt δ / Real.sqrt ν * ‖u (T - δ)‖ := by
    simpa only [sub_add_cancel] using hFmass0
  have hM0 : ∀ s ∈ Ioc (T - δ) T,
      0 ≤ heatHalfGeneratorMoment (u s) := by
    intro s _hs
    exact heatHalfGeneratorMoment_nonneg (u s)
  have hvolterra0 := averaged_splitVolterra_of_literalConvolution
    (M := fun s => heatHalfGeneratorMoment (u s))
    (F := restartFreeHalfMomentMajorant ν (T - δ) (u (T - δ)))
    hν hR hδ0 hδT hmoment hFint hM0 hpoint
  rw [hFmass] at hvolterra0
  exact positiveRestart_graph_X2_and_terminal_X1_of_halfGeneratorDomain
    ν hν u₀ u huc hu hR hT hδ hδT huR hmild hhalf hmoment
    hintX1 hmassX1 hsmall hvolterra0

end Navier.Analysis.LeiLinPositiveRestartBootstrap

#print axioms Navier.Analysis.LeiLinPositiveRestartBootstrap.integral_truncatedVolterraConvolution
#print axioms Navier.Analysis.LeiLinPositiveRestartBootstrap.heatHalfGeneratorMoment_weightedHeatFlow_le_restartFree
#print axioms Navier.Analysis.LeiLinPositiveRestartBootstrap.averaged_splitVolterra_of_literalConvolution
#print axioms Navier.Analysis.LeiLinPositiveRestartBootstrap.exists_smallCoefficient_integrableMoment_with_nonintegrableKernelProduct
#print axioms Navier.Analysis.LeiLinPositiveRestartBootstrap.positiveRestart_graph_X2_and_terminal_X1_of_literalSplitVolterra
