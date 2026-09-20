import Navier.Analysis.RestartBKMConsumer
import Navier.Analysis.ViscosityAdmissibility

/-!
# Normalize the local-existence leaf to viscosity one

The BKM/restart consumer currently retains `LocalClassicalExistence`, whose
outer quantifier ranges over every positive viscosity.  The repository already
transports the full global solution contract across viscosity, but its local
`SolvesBefore` carrier had no corresponding bridge.

This module supplies that bridge.  Scaling

`uₐ(t,x) = a u(a t,x)`, `pₐ(t,x) = a² p(a t,x)`

maps a solution before `T` at viscosity `μ` to a solution before `T/a` at
viscosity `a μ`.  Smoothness, the pointwise equation, finite slice energy, and
the initial-energy inequality are all transported.  Consequently the full
local-existence leaf is equivalent to its viscosity-one surface.  The final
theorem consumes that normalized leaf in the checked BKM/restart crown
endpoint; the uniform BKM and restart inputs remain explicit.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff ENNReal Matrix NNReal
open MeasureTheory Set

namespace Navier.Analysis.LocalExistenceViscosityReduction

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste
open Navier.Analysis.RestartBKMConsumer
open Navier.Analysis.ViscosityTransport
open Navier.Analysis.ViscosityAdmissibility
open Navier.Analysis.Vorticity

/-- The time-dilation map sends the scaled half-open horizon into the original
half-open horizon. -/
theorem mapsTo_spacetimeBefore_viscosityTimeMap
    (a T : ℝ) (ha : 0 < a) :
    MapsTo (viscosityTimeMap a) (spacetimeBefore (T / a))
      (spacetimeBefore T) := by
  intro z hz
  refine ⟨⟨mul_nonneg ha.le hz.1.1, ?_⟩, hz.2⟩
  have h := (lt_div_iff₀ ha).mp hz.1.2
  change a * z.1 < T
  simpa only [mul_comm] using h

/-- Joint velocity smoothness transports to the divided horizon. -/
theorem smoothVelocityBefore_viscosityScaled
    (a T : ℝ) (ha : 0 < a) (u : VelocityEvolution)
    (hu : SmoothVelocityBefore T u) :
    SmoothVelocityBefore (T / a) (viscosityScaledVelocity a u) := by
  have hcomp := hu.comp (contDiff_viscosityTimeMap a).contDiffOn
    (mapsTo_spacetimeBefore_viscosityTimeMap a T ha)
  have hscaled := hcomp.const_smul a
  simpa only [SmoothVelocityBefore, viscosityScaledVelocity,
    viscosityTimeMap, Function.comp_apply] using hscaled

/-- Joint pressure smoothness transports to the divided horizon. -/
theorem smoothPressureBefore_viscosityScaled
    (a T : ℝ) (ha : 0 < a) (p : PressureEvolution)
    (hp : SmoothPressureBefore T p) :
    SmoothPressureBefore (T / a) (viscosityScaledPressure a p) := by
  have hcomp := hp.comp (contDiff_viscosityTimeMap a).contDiffOn
    (mapsTo_spacetimeBefore_viscosityTimeMap a T ha)
  have hscaled := hcomp.const_smul (a ^ 2)
  simpa only [SmoothPressureBefore, viscosityScaledPressure,
    viscosityTimeMap, Function.comp_apply, smul_eq_mul] using hscaled

/-- The pointwise PDE on a half-open horizon transports with viscosity weight
one and horizon weight minus one. -/
theorem satisfiesNavierStokesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (f : ForceField) (u : VelocityEvolution) (p : PressureEvolution)
    (hEquation : SatisfiesNavierStokesBefore mu f T u p) :
    SatisfiesNavierStokesBefore (a * mu) (viscosityScaledForce a f)
      (T / a) (viscosityScaledVelocity a u)
      (viscosityScaledPressure a p) := by
  intro t ht htT x
  have hScaledTime : 0 ≤ a * t := mul_nonneg ha.le ht
  have hScaledBefore : a * t < T := by
    have h := (lt_div_iff₀ ha).mp htT
    simpa only [mul_comm] using h
  have hAtScaledPoint := hEquation (a * t) hScaledTime hScaledBefore x
  rw [timeDerivative_viscosityScaled a ha u t ht x]
  rw [convection_viscosityScaled, laplacian_viscosityScaled,
    pressureGradient_viscosityScaled]
  change
    a ^ 2 • timeDerivative u (a * t) x +
        a ^ 2 • convection u (a * t) x =
      (a * mu) • (a • laplacian u (a * t) x) -
          a ^ 2 • pressureGradient p (a * t) x +
        a ^ 2 • f (a * t) x
  rw [← smul_add, hAtScaledPoint]
  simp only [smul_add, smul_sub, smul_smul]
  congr 1
  ring_nf

/-- The four local classical PDE clauses transport to the divided horizon. -/
theorem originalSolvesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution)
    (h : OriginalSolvesBefore mu T u p) :
    OriginalSolvesBefore (a * mu) (T / a)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p) := by
  rcases h with ⟨hu, hp, hinc, heq⟩
  refine ⟨smoothVelocityBefore_viscosityScaled a T ha u hu,
    smoothPressureBefore_viscosityScaled a T ha p hp, ?_, ?_⟩
  · intro t ht htT x
    have hScaledBefore : a * t < T := by
      have h' := (lt_div_iff₀ ha).mp htT
      simpa only [mul_comm] using h'
    rw [divergence_viscosityScaled,
      hinc (a * t) (mul_nonneg ha.le ht) hScaledBefore x, mul_zero]
  · simpa only [viscosityScaledForce_zero] using
      satisfiesNavierStokesBefore_viscosityScaled_mul
        a ha mu T zeroForce u p heq

/-- The full admissible local solution class transports across viscosity.
The energy inequality is unchanged after multiplying both sides by `a²`. -/
theorem solvesBefore_viscosityScaled_mul
    (a : ℝ) (ha : 0 < a) (mu T : ℝ)
    (u : VelocityEvolution) (p : PressureEvolution)
    (h : SolvesBefore mu T u p) :
    SolvesBefore (a * mu) (T / a)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p) where
  classical := originalSolvesBefore_viscosityScaled_mul a ha mu T u p h.classical
  finite_energy := by
    intro t ht htT
    apply finiteEnergy_viscosityScaled a ha u t
    apply h.finite_energy (a * t) (mul_nonneg ha.le ht)
    have h' := (lt_div_iff₀ ha).mp htT
    simpa only [mul_comm] using h'
  energy_le_initial := by
    intro t ht htT
    rw [kineticEnergy_viscosityScaled a ha,
      kineticEnergy_viscosityScaled a ha]
    simp only [mul_zero]
    apply mul_le_mul_of_nonneg_left
    · apply h.energy_le_initial (a * t) (mul_nonneg ha.le ht)
      have h' := (lt_div_iff₀ ha).mp htT
      simpa only [mul_comm] using h'
    · positivity

/-! ## The BKM control is viscosity-scale invariant -/

/-- Vorticity has amplitude weight one under the time/amplitude viscosity
rescaling. -/
theorem vorticity_viscosityScaled (a : ℝ) (u : VelocityEvolution)
    (t : ℝ) (x : Space) :
    vorticity (viscosityScaledVelocity a u) t x =
      a • vorticity u (a * t) x := by
  simp only [vorticity, staticCurl]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show fderiv ℝ ((viscosityScaledVelocity a u) t) x =
      spatialDerivative (viscosityScaledVelocity a u) t x by rfl]
  rw [spatialDerivative_viscosityScaled]
  exact (crossProduct (basisVector i)).map_smul a _

/-- The extended-real spatial vorticity supremum has the same amplitude
weight. -/
theorem vorticityRate_viscosityScaled
    (a : ℝ) (ha : 0 < a) (u : VelocityEvolution) (t : ℝ) :
    vorticityRate (viscosityScaledVelocity a u) t =
      ENNReal.ofReal a * vorticityRate u (a * t) := by
  unfold vorticityRate
  simp_rw [vorticity_viscosityScaled, officialEuclideanNorm_smul,
    abs_of_pos ha, ENNReal.ofReal_mul ha.le]
  exact (ENNReal.mul_iSup _ _).symm

/-- Multiplication by a positive scalar pushes Lebesgue measure to the
inverse-weighted Lebesgue measure. -/
theorem measurePreserving_mul
    (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (fun t : ℝ => a * t) volume
      ((ENNReal.ofReal a)⁻¹ • volume) := by
  refine ⟨measurable_const_mul a, ?_⟩
  rw [show (fun t : ℝ => a * t) = (fun t : ℝ => a • t) by rfl]
  rw [Measure.map_addHaar_smul volume ha.ne']
  simp [Module.finrank_self, abs_of_pos ha, ENNReal.ofReal_inv_of_pos ha]

/-- The time-amplitude factors in the BKM integral cancel exactly. -/
theorem setLIntegral_vorticityScale
    (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ≥0∞) (s : ℝ) :
    ∫⁻ t in Icc 0 s, ENNReal.ofReal a * f (a * t) =
      ∫⁻ r in Icc 0 (a * s), f r := by
  have hpre : (fun t : ℝ => a * t) ⁻¹' Icc 0 (a * s) = Icc 0 s := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h0, hs⟩
      exact ⟨(mul_nonneg_iff_of_pos_left ha |>.mp <| h0), by nlinarith⟩
    · rintro ⟨h0, hs⟩
      exact ⟨mul_nonneg ha.le h0, by nlinarith⟩
  have hemb : MeasurableEmbedding (fun t : ℝ => a * t) := by
    exact (continuous_const.mul continuous_id).measurableEmbedding
      (by intro x y h; exact mul_left_cancel₀ ha.ne' h)
  have hchange := (measurePreserving_mul a ha).setLIntegral_comp_preimage_emb
    hemb f (Icc 0 (a * s))
  rw [hpre] at hchange
  rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal a) _ ENNReal.ofReal_ne_top,
    hchange, Measure.restrict_smul, MeasureTheory.lintegral_smul_measure]
  rw [smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel]
  · exact one_mul _
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  · exact ENNReal.ofReal_ne_top

/-- The BKM vorticity-integral quantity is invariant when the horizon is
scaled contragrediently to the viscosity time dilation. -/
theorem bkmVorticityControl_viscosityScaled
    (a : ℝ) (ha : 0 < a) (T : ℝ) (u : VelocityEvolution) :
    bkmVorticityControl (T / a) (viscosityScaledVelocity a u) =
      bkmVorticityControl T u := by
  unfold bkmVorticityControl
  simp_rw [vorticityRate_viscosityScaled a ha]
  simp_rw [setLIntegral_vorticityScale a ha]
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    have has : a * s ∈ Ico (0 : ℝ) T := by
      have hsT := (lt_div_iff₀ ha).mp hs.2
      exact ⟨mul_nonneg ha.le hs.1, by simpa only [mul_comm] using hsT⟩
    exact le_iSup₂_of_le (a * s) has le_rfl
  · refine iSup₂_le fun r hr => ?_
    have hs : r / a ∈ Ico (0 : ℝ) (T / a) :=
      ⟨div_nonneg hr.1 ha.le, (div_lt_div_iff_of_pos_right ha).mpr hr.2⟩
    have har : a * (r / a) = r := by field_simp
    simpa only [har] using
      (le_iSup₂_of_le (r / a) hs le_rfl :
        (∫⁻ t in Icc 0 (a * (r / a)), vorticityRate u t) ≤
          ⨆ s ∈ Ico (0 : ℝ) (T / a),
            ∫⁻ t in Icc 0 (a * s), vorticityRate u t)

/-- The exact unit-viscosity surface of the local-existence leaf. -/
def LocalClassicalExistenceAtViscosityOne : Prop :=
  ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore 1 T u p

/-- Local classical existence for all positive viscosities is equivalent to
its unit-viscosity surface.  The reverse implication applies unit-viscosity
existence to the inverse-amplitude datum and scales the resulting local
solution forward. -/
theorem localClassicalExistence_iff_atViscosityOne :
    LocalClassicalExistence ↔ LocalClassicalExistenceAtViscosityOne := by
  constructor
  · intro h u₀ hu₀
    exact h 1 zero_lt_one u₀ hu₀
  · intro h nu hnu u₀ hu₀
    let base := viscosityScaledSchwartzDatum nu⁻¹ u₀
    have hbase : DivergenceFreeInitial base :=
      divergenceFreeInitial_viscosityScaledSchwartzDatum nu⁻¹ u₀ hu₀
    rcases h base hbase with ⟨T, hT, u, p, hinit, hsol⟩
    refine ⟨T / nu, div_pos hT hnu,
      viscosityScaledVelocity nu u, viscosityScaledPressure nu p, ?_, ?_⟩
    · intro x
      have hscaled := initialCondition_viscosityScaledSchwartz nu base u hinit x
      simpa only [base, viscosityScaledSchwartzDatum, smul_smul,
        mul_inv_cancel₀ hnu.ne', one_smul] using hscaled
    · simpa only [mul_one] using
        solvesBefore_viscosityScaled_mul nu hnu 1 T u p hsol

/-- The viscosity-normalized local leaf is consumed directly by the checked
BKM/restart whole-space endpoint.  Only the viscosity parameter has been
discharged; the unit-viscosity local theorem, uniform BKM estimate, and restart
engine remain explicit. -/
theorem wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
    (hlocal : LocalClassicalExistenceAtViscosityOne)
    (hbkm : NSBKMUniformVorticityApriori)
    (hrestart : HorizonIndependentRestart bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  exact wholeSpaceGlobalRegularity_of_local_bkmRestart
      (localClassicalExistence_iff_atViscosityOne.mpr hlocal) hbkm hrestart

/-- The exact unit-viscosity surface of the solution-uniform, horizon-uniform
BKM a priori leaf. -/
def NSBKMUniformVorticityAprioriAtViscosityOne : Prop :=
  ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ M : ℝ≥0, ∀ T : ℝ, 0 < T →
      ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore 1 T u p →
          bkmVorticityControl T u ≤ (M : ℝ≥0∞)

/-- The all-positive-viscosity BKM a priori leaf is equivalent to its
unit-viscosity surface.  The reverse direction rescales each supplied local
solution back to viscosity one; exact invariance of `bkmVorticityControl`
then transfers the unit-viscosity budget without changing its value. -/
theorem nsBKMUniformVorticityApriori_iff_atViscosityOne :
    NSBKMUniformVorticityApriori ↔
      NSBKMUniformVorticityAprioriAtViscosityOne := by
  constructor
  · intro h u₀ hu₀
    exact h 1 zero_lt_one u₀ hu₀
  · intro h nu hnu u₀ hu₀
    let a := nu⁻¹
    have ha : 0 < a := inv_pos.mpr hnu
    let base := viscosityScaledSchwartzDatum a u₀
    have hbase : DivergenceFreeInitial base :=
      divergenceFreeInitial_viscosityScaledSchwartzDatum a u₀ hu₀
    obtain ⟨M, hM⟩ := h base hbase
    refine ⟨M, ?_⟩
    intro T hT u p hinit hsol
    have hinitScaled : ∀ x : Space,
        viscosityScaledVelocity a u 0 x = base x := by
      simpa only [base] using
        initialCondition_viscosityScaledSchwartz a u₀ u hinit
    have hsolScaled : SolvesBefore 1 (T / a)
        (viscosityScaledVelocity a u) (viscosityScaledPressure a p) := by
      simpa only [a, inv_mul_cancel₀ hnu.ne'] using
        solvesBefore_viscosityScaled_mul a ha nu T u p hsol
    have hbound := hM (T / a) (div_pos hT ha)
      (viscosityScaledVelocity a u) (viscosityScaledPressure a p)
      hinitScaled hsolScaled
    rw [bkmVorticityControl_viscosityScaled a ha T u] at hbound
    exact hbound

/-- The checked whole-space consumer with both local existence and the BKM
a priori estimate normalized to viscosity one.  The same-quantity restart
engine remains the sole all-viscosity hypothesis. -/
theorem wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_restart
    (hlocal : LocalClassicalExistenceAtViscosityOne)
    (hbkm : NSBKMUniformVorticityAprioriAtViscosityOne)
    (hrestart : HorizonIndependentRestart bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  exact wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart hlocal
    (nsBKMUniformVorticityApriori_iff_atViscosityOne.mpr hbkm) hrestart

end Navier.Analysis.LocalExistenceViscosityReduction

set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.localClassicalExistence_iff_atViscosityOne
set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.bkmVorticityControl_viscosityScaled
set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.nsBKMUniformVorticityApriori_iff_atViscosityOne
set_option pp.fullNames true in
#check @Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_restart
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.localClassicalExistence_iff_atViscosityOne
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.bkmVorticityControl_viscosityScaled
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.nsBKMUniformVorticityApriori_iff_atViscosityOne
set_option pp.fullNames true in
#print axioms Navier.Analysis.LocalExistenceViscosityReduction.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_restart
