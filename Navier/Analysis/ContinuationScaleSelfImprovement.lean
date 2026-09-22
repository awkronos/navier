import Navier.Analysis.LocalExistenceViscosityReduction
import Navier.Analysis.RestartEnergyControl
import Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown

/-!
# The datum-uniform continuation leaf self-improves under parabolic zoom

`NormalizedContinuationFromCriticalControl N` chooses the continuation step
`δ = δ(ν, M)` before the datum.  The admissible class `SolvesBefore` is
invariant under the parabolic dilation

`u_λ(t,x) = λ u(λ²t, λx)`,  `p_λ(t,x) = λ² p(λ²t, λx)`,

which sends a solution before `T` to a solution before `T/λ²` at the SAME
viscosity (`solvesBefore_parabolicScaled`), preserves the normalized pressure
gauge and maps Schwartz divergence-free data to Schwartz divergence-free data.
For a quantity that does not increase under zoom (`ZoomMonotone N`), zooming a
solution in by `μ ≥ 1`, applying the datum-uniform step `δ`, and zooming back
out extends the original solution by `μ²δ`.  Since `μ` is free, the leaf is
equivalent to continuation by EVERY step length
(`normalizedContinuation_iff_arbitraryStep`).

Both concrete quantities the repository consumes are zoom-monotone:

* `bkmVorticityControl` is exactly zoom-invariant
  (`bkmVorticityControl_parabolicScaled`);
* `preterminalEnergyControl` scales by `λ⁻¹` (energy is supercritical), so it
  decreases under zoom-in (`preterminalEnergyControl_parabolicScaled_le`).

Consequently the datum-uniform restart leaves of the two restart endpoints,
`HorizonIndependentRestart bkmVorticityControl` and
`HorizonIndependentRestart preterminalEnergyControl`, each assert that every
admissible solution with finite control extends to every longer horizon: they
are not strictly weaker than the crown's continuation content (lean4-bans
B9a(ii)).  The repair is the datum-dependent leaf
`DatumHorizonIndependentRestart` (`RestartPaste`), whose step is chosen after
the datum; the zoom changes the datum, so the argument above does not apply to
it, and the gluing composition
`wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori` consumes it.
The final theorem wires that weaker leaf into the viscosity-one BKM endpoint.

Scope: nothing here proves or refutes any restart leaf.  The truth status of
`DatumHorizonIndependentRestart bkmVorticityControl` on the full
`SolvesBefore` class (which imposes no spatial decay beyond finite energy) is
open in this repository.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff ENNReal NNReal
open MeasureTheory Set

namespace Navier.Analysis.ContinuationScaleSelfImprovement

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste
open Navier.Analysis.RestartEnergyControl
open Navier.Analysis.Covariance
open Navier.Analysis.Vorticity
open Navier.Analysis.ViscosityTransport
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.LocalExistenceViscosityReduction
open Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown

/-! ## Parabolic dilation of the half-open solution class -/

theorem mapsTo_spacetimeBefore_parabolicCLM
    (lambda T : ℝ) (hl : 0 < lambda) :
    MapsTo (parabolicCLM lambda) (spacetimeBefore (T / lambda ^ 2))
      (spacetimeBefore T) := by
  intro z hz
  have hl2 : 0 < lambda ^ 2 := by positivity
  refine ⟨⟨mul_nonneg hl2.le hz.1.1, ?_⟩, Set.mem_univ _⟩
  have h := (lt_div_iff₀ hl2).mp hz.1.2
  change lambda ^ 2 * z.1 < T
  linarith [mul_comm z.1 (lambda ^ 2)]

theorem smoothVelocityBefore_parabolicScaled
    {lambda T : ℝ} (hl : 0 < lambda) {u : VelocityEvolution}
    (hu : SmoothVelocityBefore T u) :
    SmoothVelocityBefore (T / lambda ^ 2) (parabolicScaledVelocity lambda u) := by
  have hcomp := hu.comp (parabolicCLM lambda).contDiff.contDiffOn
    (mapsTo_spacetimeBefore_parabolicCLM lambda T hl)
  refine (hcomp.const_smul lambda).congr ?_
  intro z _
  rfl

theorem smoothPressureBefore_parabolicScaled
    {lambda T : ℝ} (hl : 0 < lambda) {p : PressureEvolution}
    (hp : SmoothPressureBefore T p) :
    SmoothPressureBefore (T / lambda ^ 2) (parabolicScaledPressure lambda p) := by
  have hcomp := hp.comp (parabolicCLM lambda).contDiff.contDiffOn
    (mapsTo_spacetimeBefore_parabolicCLM lambda T hl)
  refine (hcomp.const_smul (lambda ^ 2)).congr ?_
  intro z _
  rfl

theorem scaledTime_mem {lambda T t : ℝ} (hl : 0 < lambda) (ht : 0 ≤ t)
    (htT : t < T / lambda ^ 2) :
    0 ≤ lambda ^ 2 * t ∧ lambda ^ 2 * t < T := by
  have hl2 : 0 < lambda ^ 2 := by positivity
  refine ⟨mul_nonneg hl2.le ht, ?_⟩
  have h := (lt_div_iff₀ hl2).mp htT
  linarith [mul_comm t (lambda ^ 2)]

theorem satisfiesNavierStokesBefore_parabolicScaled
    {lambda : ℝ} (hl : 0 < lambda) {ν T : ℝ}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : SatisfiesNavierStokesBefore ν zeroForce T u p) :
    SatisfiesNavierStokesBefore ν zeroForce (T / lambda ^ 2)
      (parabolicScaledVelocity lambda u) (parabolicScaledPressure lambda p) := by
  intro t ht htT x
  obtain ⟨hts, htsT⟩ := scaledTime_mem hl ht htT
  have hat := h (lambda ^ 2 * t) hts htsT (lambda • x)
  rw [timeDerivative_scaled lambda hl u t ht x, convection_scaled, laplacian_scaled,
    pressureGradient_scaled]
  simp only [zeroForce, add_zero] at hat ⊢
  rw [← smul_add, hat]
  simp only [smul_sub, smul_smul]
  rw [mul_comm (lambda ^ 3) ν]

theorem solvesBefore_parabolicScaled
    {lambda : ℝ} (hl : 0 < lambda) {ν T : ℝ}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : SolvesBefore ν T u p) :
    SolvesBefore ν (T / lambda ^ 2)
      (parabolicScaledVelocity lambda u) (parabolicScaledPressure lambda p) := by
  obtain ⟨⟨hv, hp, hin, heq⟩, hfe, hel⟩ := h
  refine ⟨⟨smoothVelocityBefore_parabolicScaled hl hv,
    smoothPressureBefore_parabolicScaled hl hp, ?_,
    satisfiesNavierStokesBefore_parabolicScaled hl heq⟩, ?_, ?_⟩
  · intro t ht htT x
    obtain ⟨hts, htsT⟩ := scaledTime_mem hl ht htT
    rw [divergence_scaled, hin (lambda ^ 2 * t) hts htsT]
    exact mul_zero _
  · intro t ht htT
    obtain ⟨hts, htsT⟩ := scaledTime_mem hl ht htT
    have hf := hfe (lambda ^ 2 * t) hts htsT
    have hpt : (fun x : Space =>
        ‖parabolicScaledVelocity lambda u t x‖ ^ 2) =
        fun x : Space => (lambda ^ 2 : ℝ) •
          ((fun y : Space => ‖u (lambda ^ 2 * t) y‖ ^ 2) (lambda • x)) := by
      funext x
      simp only [parabolicScaledVelocity, norm_smul, Real.norm_eq_abs,
        abs_of_pos hl, pow_two, smul_eq_mul]
      ring
    rw [hpt]
    exact MeasureTheory.Integrable.smul (lambda ^ 2)
      ((MeasureTheory.integrable_comp_smul_iff volume
          (fun y : Space => ‖u (lambda ^ 2 * t) y‖ ^ 2) hl.ne').mpr hf)
  · intro t ht htT
    obtain ⟨hts, htsT⟩ := scaledTime_mem hl ht htT
    rw [kineticEnergy_parabolicScaled lambda hl u t,
      kineticEnergy_parabolicScaled lambda hl u 0, mul_zero]
    exact mul_le_mul_of_nonneg_left (hel (lambda ^ 2 * t) hts htsT)
      (inv_pos.mpr hl).le

theorem pressureNormalizedBefore_parabolicScaled
    {lambda T : ℝ} (hl : 0 < lambda) {p : PressureEvolution}
    (h : PressureNormalizedBefore T p) :
    PressureNormalizedBefore (T / lambda ^ 2) (parabolicScaledPressure lambda p) := by
  intro t ht htT
  obtain ⟨hts, htsT⟩ := scaledTime_mem hl ht htT
  show lambda ^ 2 * p (lambda ^ 2 * t) (lambda • (0 : Space)) = 0
  rw [smul_zero, h (lambda ^ 2 * t) hts htsT, mul_zero]

theorem parabolicScaledVelocity_comp (lambda mu : ℝ) (u : VelocityEvolution) :
    parabolicScaledVelocity mu (parabolicScaledVelocity lambda u) =
      parabolicScaledVelocity (lambda * mu) u := by
  funext t x
  have h1 : lambda ^ 2 * (mu ^ 2 * t) = (lambda * mu) ^ 2 * t := by ring
  simp only [parabolicScaledVelocity, smul_smul]
  rw [h1, mul_comm mu lambda]

theorem parabolicScaledPressure_comp (lambda mu : ℝ) (p : PressureEvolution) :
    parabolicScaledPressure mu (parabolicScaledPressure lambda p) =
      parabolicScaledPressure (lambda * mu) p := by
  funext t x
  simp only [parabolicScaledPressure, smul_smul]
  rw [show lambda ^ 2 * (mu ^ 2 * t) = (lambda * mu) ^ 2 * t by ring,
    mul_comm lambda mu]
  ring

@[simp] theorem parabolicScaledVelocity_one (u : VelocityEvolution) :
    parabolicScaledVelocity 1 u = u := by
  funext t x
  simp [parabolicScaledVelocity]

@[simp] theorem parabolicScaledPressure_one (p : PressureEvolution) :
    parabolicScaledPressure 1 p = p := by
  funext t x
  simp [parabolicScaledPressure]

/-! ## Zoom behaviour of the two consumed control quantities -/

/-- The spatial vorticity supremum has parabolic weight `λ²` and time
argument `λ²t`; the spatial dilation is absorbed by the supremum. -/
theorem vorticityRate_parabolicScaled
    {lambda : ℝ} (hl : 0 < lambda) (u : VelocityEvolution) (t : ℝ) :
    vorticityRate (parabolicScaledVelocity lambda u) t =
      vorticityRate (viscosityScaledVelocity (lambda ^ 2) u) t := by
  have hl2 : 0 < lambda ^ 2 := by positivity
  rw [vorticityRate_viscosityScaled _ hl2]
  unfold vorticityRate
  simp_rw [vorticity_scaled, officialEuclideanNorm_smul, abs_of_pos hl2,
    ENNReal.ofReal_mul hl2.le]
  rw [← ENNReal.mul_iSup]
  congr 1
  have hsurj : Function.Surjective (fun x : Space => lambda • x) := by
    intro y
    exact ⟨lambda⁻¹ • y, by simp [smul_smul, mul_inv_cancel₀ hl.ne']⟩
  exact hsurj.iSup_comp
    (fun y : Space => ENNReal.ofReal
      (officialEuclideanNorm (vorticity u (lambda ^ 2 * t) y)))

/-- **The BKM quantity is exactly invariant under parabolic zoom.** -/
theorem bkmVorticityControl_parabolicScaled
    {lambda : ℝ} (hl : 0 < lambda) (T : ℝ) (u : VelocityEvolution) :
    bkmVorticityControl (T / lambda ^ 2) (parabolicScaledVelocity lambda u) =
      bkmVorticityControl T u := by
  have hl2 : 0 < lambda ^ 2 := by positivity
  rw [← bkmVorticityControl_viscosityScaled (lambda ^ 2) hl2 T u]
  unfold bkmVorticityControl
  simp_rw [vorticityRate_parabolicScaled hl]

theorem kineticEnergy_nonneg' (u : VelocityEvolution) (t : ℝ) :
    0 ≤ kineticEnergy u t := by
  unfold kineticEnergy
  exact integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg (u t x i)))

/-- **The preterminal energy supremum does not increase under zoom-in.**
Energy is supercritical: it scales by `λ⁻¹ ≤ 1`. -/
theorem preterminalEnergyControl_parabolicScaled_le
    {lambda : ℝ} (hl : 1 ≤ lambda) (T : ℝ) (u : VelocityEvolution) :
    preterminalEnergyControl (T / lambda ^ 2) (parabolicScaledVelocity lambda u) ≤
      preterminalEnergyControl T u := by
  have hl0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hl
  unfold preterminalEnergyControl
  refine iSup₂_le (fun t ht => ?_)
  obtain ⟨hts, htsT⟩ := scaledTime_mem hl0 ht.1 ht.2
  refine le_iSup₂_of_le (lambda ^ 2 * t) ⟨hts, htsT⟩ ?_
  rw [kineticEnergy_parabolicScaled lambda hl0 u t]
  apply ENNReal.ofReal_le_ofReal
  have hE := kineticEnergy_nonneg' u (lambda ^ 2 * t)
  have hinv : lambda⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl
  nlinarith

/-! ## Self-improvement of the datum-uniform leaf -/

/-- A control quantity that does not increase when a solution is zoomed in
(`λ ≥ 1`, horizon divided by `λ²`). -/
def ZoomMonotone (N : CriticalQuantity) : Prop :=
  ∀ lambda : ℝ, 1 ≤ lambda → ∀ T : ℝ, ∀ u : VelocityEvolution,
    N (T / lambda ^ 2) (parabolicScaledVelocity lambda u) ≤ N T u

theorem zoomMonotone_bkmVorticityControl : ZoomMonotone bkmVorticityControl :=
  fun _lambda hl T u =>
    (bkmVorticityControl_parabolicScaled (lt_of_lt_of_le zero_lt_one hl) T u).le

theorem zoomMonotone_preterminalEnergyControl :
    ZoomMonotone preterminalEnergyControl :=
  fun _lambda hl T u => preterminalEnergyControl_parabolicScaled_le hl T u

/-- Continuation of every admissible solution with control at most `M` by an
ARBITRARY prescribed step `L`, uniformly in the datum and the horizon. -/
def ArbitraryStepContinuation (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∀ L : ℝ, 0 < L →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + L) u' p' ∧
            PressureNormalizedBefore (T + L) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p'

/-- **Zoom self-improvement.**  For a zoom-monotone quantity the datum-uniform
continuation step can be taken arbitrarily long: zoom in by `μ = L/δ + 1`,
take the step `δ`, zoom back out. -/
theorem arbitraryStep_of_normalizedContinuation {N : CriticalQuantity}
    (hZ : ZoomMonotone N) (h : NormalizedContinuationFromCriticalControl N) :
    ArbitraryStepContinuation N := by
  intro ν hν M L hL u₀ hdiv T hT u p hinit hsol hnorm hN
  obtain ⟨δ, hδ, hstep⟩ := h ν hν M
  set μ : ℝ := L / δ + 1 with hμ_def
  have hLδ : 0 < L / δ := div_pos hL hδ
  have hμ1 : 1 ≤ μ := by linarith
  have hμ0 : 0 < μ := by linarith
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hvsol := solvesBefore_parabolicScaled hμ0 hsol
  have hvnorm := pressureNormalizedBefore_parabolicScaled hμ0 hnorm
  have hvinit : ∀ x : Space, parabolicScaledVelocity μ u 0 x =
      scaledSchwartzVelocity μ u₀ x := by
    intro x
    show μ • u (μ ^ 2 * 0) (μ • x) = scaledSchwartzVelocity μ u₀ x
    rw [mul_zero, hinit, scaledSchwartzVelocity_apply]
  have hvN : N (T / μ ^ 2) (parabolicScaledVelocity μ u) ≤ (M : ℝ≥0∞) :=
    (hZ μ hμ1 T u).trans hN
  obtain ⟨v', q', hsol', hnorm', hagv, hagq⟩ :=
    hstep (scaledSchwartzVelocity μ u₀) (divergenceFreeInitial_scaled μ u₀ hdiv)
      (T / μ ^ 2) (div_pos hT hμ2) _ _ hvinit hvsol hvnorm hvN
  have hμi : 0 < μ⁻¹ := inv_pos.mpr hμ0
  have hback := solvesBefore_parabolicScaled hμi hsol'
  have hbacknorm := pressureNormalizedBefore_parabolicScaled hμi hnorm'
  have hhor : (T / μ ^ 2 + δ) / μ⁻¹ ^ 2 = T + μ ^ 2 * δ := by
    field_simp
  rw [hhor] at hback hbacknorm
  have hstepL : T + L ≤ T + μ ^ 2 * δ := by
    have hμδ : L ≤ μ * δ := by
      rw [hμ_def, add_mul, div_mul_cancel₀ L hδ.ne']
      linarith
    have : μ * δ ≤ μ ^ 2 * δ := by nlinarith
    linarith
  refine ⟨parabolicScaledVelocity μ⁻¹ v', parabolicScaledPressure μ⁻¹ q',
    hback.mono hstepL, fun t ht htT => hbacknorm t ht (lt_of_lt_of_le htT hstepL),
    ?_, ?_⟩
  · intro t ht htT
    have hs : 0 ≤ μ⁻¹ ^ 2 * t := mul_nonneg (by positivity) ht
    have hsT : μ⁻¹ ^ 2 * t < T / μ ^ 2 := by
      rw [inv_pow, lt_div_iff₀ hμ2]
      field_simp
      exact htT
    have hid : u t = parabolicScaledVelocity μ⁻¹ (parabolicScaledVelocity μ u) t := by
      rw [parabolicScaledVelocity_comp, mul_inv_cancel₀ hμ0.ne',
        parabolicScaledVelocity_one]
    rw [hid]
    funext x
    show μ⁻¹ • parabolicScaledVelocity μ u (μ⁻¹ ^ 2 * t) (μ⁻¹ • x) =
      μ⁻¹ • v' (μ⁻¹ ^ 2 * t) (μ⁻¹ • x)
    rw [hagv (μ⁻¹ ^ 2 * t) hs hsT]
  · intro t ht htT
    have hs : 0 ≤ μ⁻¹ ^ 2 * t := mul_nonneg (by positivity) ht
    have hsT : μ⁻¹ ^ 2 * t < T / μ ^ 2 := by
      rw [inv_pow, lt_div_iff₀ hμ2]
      field_simp
      exact htT
    have hid : p t = parabolicScaledPressure μ⁻¹ (parabolicScaledPressure μ p) t := by
      rw [parabolicScaledPressure_comp, mul_inv_cancel₀ hμ0.ne',
        parabolicScaledPressure_one]
    rw [hid]
    funext x
    show μ⁻¹ ^ 2 * parabolicScaledPressure μ p (μ⁻¹ ^ 2 * t) (μ⁻¹ • x) =
      μ⁻¹ ^ 2 * q' (μ⁻¹ ^ 2 * t) (μ⁻¹ • x)
    rw [hagq (μ⁻¹ ^ 2 * t) hs hsT]

/-- For a zoom-monotone quantity the datum-uniform continuation leaf is
EQUIVALENT to continuation by every step length. -/
theorem normalizedContinuation_iff_arbitraryStep {N : CriticalQuantity}
    (hZ : ZoomMonotone N) :
    NormalizedContinuationFromCriticalControl N ↔ ArbitraryStepContinuation N := by
  refine ⟨arbitraryStep_of_normalizedContinuation hZ, fun h ν hν M => ?_⟩
  exact ⟨1, one_pos, fun u₀ hdiv T hT u p hinit hsol hnorm hN =>
    h ν hν M 1 one_pos u₀ hdiv T hT u p hinit hsol hnorm hN⟩

/-- The datum-uniform BKM restart engine asserts arbitrary-step continuation
of every admissible solution with finite BKM integral. -/
theorem arbitraryStep_bkm_of_horizonIndependentRestart
    (h : HorizonIndependentRestart bkmVorticityControl) :
    ArbitraryStepContinuation bkmVorticityControl :=
  arbitraryStep_of_normalizedContinuation zoomMonotone_bkmVorticityControl
    (normalizedContinuation_of_horizonIndependentRestart h)

/-- The datum-uniform energy restart engine asserts arbitrary-step
continuation of every admissible solution (every one has finite preterminal
energy, bounded by its datum). -/
theorem arbitraryStep_energy_of_horizonIndependentRestart
    (h : HorizonIndependentRestart preterminalEnergyControl) :
    ArbitraryStepContinuation preterminalEnergyControl :=
  arbitraryStep_of_normalizedContinuation zoomMonotone_preterminalEnergyControl
    (normalizedContinuation_of_horizonIndependentRestart h)

/-! ## The repaired BKM endpoint -/

/-- The whole-space consumer with the restart engine in its datum-dependent
order.  Local existence and the uniform BKM budget are at viscosity one; the
restart length may depend on the datum. -/
theorem wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart
    (hlocal : LocalClassicalExistenceAtViscosityOne)
    (hbkm : NSBKMUniformVorticityAprioriAtViscosityOne)
    (hrestart : DatumHorizonIndependentRestart bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori bkmVorticityControl
    (localClassicalExistence_iff_atViscosityOne.mpr hlocal)
    (datumContinuation_of_datumRestart hrestart)
    (nsBKMUniformVorticityApriori_iff_atViscosityOne.mpr hbkm)

end Navier.Analysis.ContinuationScaleSelfImprovement

set_option pp.fullNames true in
#check @Navier.Analysis.ContinuationScaleSelfImprovement.solvesBefore_parabolicScaled
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuationScaleSelfImprovement.bkmVorticityControl_parabolicScaled
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuationScaleSelfImprovement.normalizedContinuation_iff_arbitraryStep
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.solvesBefore_parabolicScaled
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.bkmVorticityControl_parabolicScaled
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.preterminalEnergyControl_parabolicScaled_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.arbitraryStep_of_normalizedContinuation
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.normalizedContinuation_iff_arbitraryStep
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.arbitraryStep_bkm_of_horizonIndependentRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.arbitraryStep_energy_of_horizonIndependentRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart
