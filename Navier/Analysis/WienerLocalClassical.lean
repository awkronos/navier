import Navier.Analysis.WienerLocalExistence
import Navier.Analysis.WienerPressureSmooth
import Navier.Analysis.WienerPlancherel
import Navier.Analysis.WienerEnergy
import Navier.Analysis.LocalExistenceViscosityReduction
import Navier.Analysis.ContinuationScaleSelfImprovement

/-!
# Local classical existence at viscosity one

`localClassicalExistenceAtViscosityOne : LocalClassicalExistenceAtViscosityOne`.

For a divergence-free Schwartz datum `u₀`, the rescaled large-data Wiener solution
(datum `-2π u₀`, repository viscosity `4π²`, horizon `10⁶ T ‖𝓕(2πu₀)‖²_{L¹} ≤ 4π²`)
gives `u = -(2π)⁻¹ Re 𝓕⁻ w`, `p = -(4π²)⁻¹ Re 𝓕⁻ Q̂` with `u 0 = u₀` and
`SolvesBefore 1 T u p`: joint smoothness of `u` and `p`, incompressibility, the
official equation, finite-energy slices (Plancherel inequality and the
frequency-side `L∞` bound) and the energy inequality (Fourier energy decay,
Plancherel, and Schwartz Plancherel at `t = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff ComplexConjugate

namespace Navier.Analysis.WienerLocalClassical

open Navier Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSchwartzLocal
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.WienerLocalExistence
open Navier.Analysis.FourierMajorant (euclidComponent)

/-- A continuous `ℂ`-valued function with finite `L²` lintegral is square-integrable. -/
theorem integrable_norm_sq_of_lintegral {f : ES → ℂ} (hf : Continuous f)
    (h : ∫⁻ y, ‖f y‖ₑ ^ 2 ≠ ⊤) : Integrable (fun y => ‖f y‖ ^ 2) := by
  refine ⟨((continuous_norm.comp hf).pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h.lt_top
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A bounded integrable coordinate has finite `L²` lintegral. -/
theorem lintegral_sq_ne_top {f : ES → ℂ} {R : ℝ} (hf : Integrable f)
    (hb : ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ ≤ R) : ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 ≠ ⊤ := by
  have hR : ∫⁻ ξ, ENNReal.ofReal R * ‖f ξ‖ₑ ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.ne
  refine ne_top_of_le_ne_top hR (lintegral_mono_ae ?_)
  filter_upwards [hb] with ξ h
  rw [sq]
  refine mul_le_mul' ?_ le_rfl
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h

/-- Integrals over `Navier.Space` transport to the Euclidean carrier. -/
theorem integral_space_euclid (g : ES → ℝ) : ∫ x : Space, g (euclidPoint x) = ∫ y : ES, g y :=
  (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding g

theorem integrable_space_euclid {g : ES → ℝ} (hg : Integrable g) :
    Integrable (fun x : Space => g (euclidPoint x)) :=
  ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).2 hg

theorem sq_norm_le_sum (v : Space) : ‖v‖ ^ 2 ≤ ∑ k : Fin 3, (v k) ^ 2 := by
  have hs : 0 ≤ ∑ k : Fin 3, (v k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ k : Fin 3, (v k) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun k => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => (v k) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ k))
  calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ k : Fin 3, (v k) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs

theorem physU_sq_le (w : ℝ → ES → ComplexSpace) (t : ℝ) (x : Space) (k : Fin 3) :
    (physU w t x k) ^ 2 ≤ (1 / (2 * Real.pi)) ^ 2 *
      ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2 := by
  unfold physU
  rw [mul_pow, neg_sq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [sq, sq, ← abs_mul_abs_self]
  exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _) (abs_nonneg _)
    (norm_nonneg _)

theorem physU_sq_eq (w : ℝ → ES → ComplexSpace) (t : ℝ) (x : Space) (k : Fin 3)
    (him : (𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)).im = 0) :
    (physU w t x k) ^ 2 = (1 / (2 * Real.pi)) ^ 2 *
      ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2 := by
  unfold physU
  rw [mul_pow, neg_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
  ring

/-- `∫ ‖f‖² ≤ ∫ ‖g‖²` from the lintegral inequality. -/
theorem integral_sq_le_of_lintegral {f g : ES → ℂ} (hf : Integrable (fun y => ‖f y‖ ^ 2))
    (hg : Integrable (fun y => ‖g y‖ ^ 2)) (h : ∫⁻ y, ‖f y‖ₑ ^ 2 ≤ ∫⁻ y, ‖g y‖ₑ ^ 2) :
    ∫ y, ‖f y‖ ^ 2 ≤ ∫ y, ‖g y‖ ^ 2 := by
  have e : ∀ (u : ES → ℂ), Integrable (fun y => ‖u y‖ ^ 2) →
      ∫ y, ‖u y‖ ^ 2 = (∫⁻ y, ‖u y‖ₑ ^ 2).toReal := by
    intro u hu
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
      hu.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e f hf, e g hg]
  refine ENNReal.toReal_mono ?_ h
  have := hg.2
  unfold HasFiniteIntegral at this
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) this)
  show ‖g y‖ₑ ^ 2 = ‖‖g y‖ ^ 2‖ₑ
  rw [← ofReal_norm (‖g y‖ ^ 2), Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integrable_norm_sq_of_lintegral' {f : ES → ℂ} (hf : AEStronglyMeasurable f)
    (h : ∫⁻ y, ‖f y‖ₑ ^ 2 ≠ ⊤) : Integrable (fun y => ‖f y‖ ^ 2) := by
  refine ⟨(hf.norm.pow 2), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h.lt_top
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

open Navier.Analysis.WienerPointwiseODE Navier.Analysis.WienerPhysicalPDE in
/-- **Local classical existence at viscosity one.** -/
theorem localClassicalExistenceAtViscosityOne :
    Navier.Analysis.LocalExistenceViscosityReduction.LocalClassicalExistenceAtViscosityOne := by
  intro u₀ hdiv
  set v₀ : SchwartzVelocity := (-(2 * Real.pi)) • u₀ with hv₀
  set ν : ℝ := 4 * Real.pi ^ 2 with hνdef
  have hν : 0 < ν := by positivity
  set a₀ : V1 := wienerDatum v₀ with ha₀def
  set n : ℝ := ‖a₀‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set T : ℝ := ν / (10 ^ 6 * (n + 1)) with hTdef
  have hT : 0 < T := by positivity
  have hsmall6 : 10 ^ 6 * T * ‖a₀‖ ^ 2 ≤ ν := by
    rw [← hn, hTdef]
    rw [show 10 ^ 6 * (ν / (10 ^ 6 * (n + 1))) * n = ν * (n / (n + 1)) by field_simp]
    have : n / (n + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have hsmall4 : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν := by
    have : 0 ≤ T * ‖a₀‖ ^ 2 := by positivity
    nlinarith
  obtain ⟨x, hxle, hxeq, w, hxw, hfix, hG, hsm, hreal, hsym⟩ :=
    Navier.Analysis.WienerReality.exists_real_smooth_wienerSolution hν hT v₀ hsmall4
  set a : ES → ComplexSpace := fourierDatum v₀ with hadef
  -- the datum is bounded
  set A : ℝ := ∑ i : Fin 3,
    ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ with hAdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => norm_nonneg _
  have haA : ∀ ξ (i : Fin 3), ‖a ξ i‖ ≤ A := by
    intro ξ i
    have h1 : ‖a ξ i‖ ≤
        ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖ :=
      ((𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction.norm_coe_le_norm
        ξ)
    exact h1.trans (Finset.single_le_sum (f := fun i =>
      ‖(𝓕 (euclidComponent v₀ i) : SchwartzMap ES ℂ).toBoundedContinuousFunction‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i))
  have ha₀ : ∀ i, a₀ i ∈ Navier.Analysis.WienerLinfBound.Zb A := by
    intro i
    show ∀ᵐ ξ ∂(volume : Measure ES), ‖(a₀ i) ξ‖ ≤ A
    filter_upwards [coeFn_wienerDatum v₀ i] with ξ h
    rw [h]; exact haA ξ i
  have hxS := Navier.Analysis.WienerLinfBound.fixedPoint_mem_linfSet hν hT a₀ hsmall6 hA ha₀ x
    hxle hxeq
  have hRb := Navier.Analysis.WienerEnergy.ae_uniform_bound hT hν a hfix x hG.1 hxw hA
    (by positivity) hxS hxle (Eventually.of_forall fun ξ i => haA ξ i)
  set Rt : ℝ := A + 27 * (2 * A) * (2 * ‖a₀‖) * (2 * (Real.sqrt ν)⁻¹ * Real.sqrt T) with hRt
  have hR0 : 0 ≤ Rt := by positivity
  have ha : Navier.Analysis.ContinuousLeiLinReality.ProfileDivergenceFree a :=
    profileDivergenceFree_fourierDatum v₀ (divergenceFreeInitial_smul _ hdiv)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hw0 : ∀ ξ, w 0 ξ = a ξ := fun ξ => by
    rw [hfix 0 ⟨le_rfl, hT.le⟩ ξ, mild_zero]
  have hinit : ∀ x : Space, physU w 0 x = u₀ x := by
    intro x
    funext i
    have hw0i : (fun ξ => w 0 ξ i) = fun ξ => a ξ i := by
      funext ξ; rw [hw0]
    have h := physicalCoord_fourierDatum v₀ i (euclidPoint x)
    unfold physicalCoord at h
    show -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => w 0 ξ i) (euclidPoint x)).re = u₀ x i
    rw [hw0i, h, Complex.ofReal_re]
    show -(1 / (2 * Real.pi)) * ((-(2 * Real.pi)) • u₀) x i = u₀ x i
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  -- per-slice facts
  have hwint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => w t ξ k) :=
    fun t ht k => integrable_of_hmom (hmom_w hT hν hG ht k)
  have hwm : ∀ t (k : Fin 3), StronglyMeasurable (fun ξ => w t ξ k) :=
    fun t k => (continuous_apply k).comp_stronglyMeasurable (hG.1 t)
  have hwb : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES), ‖w t ξ k‖ ≤ Rt := by
    intro t ht k
    filter_upwards [hRb] with ξ h using (norm_le_pi_norm _ k).trans (h t ht)
  have hLw : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 ≠ ⊤ :=
    fun t ht k => lintegral_sq_ne_top (hwint t ht k) (hwb t ht k)
  have hPl : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      ∫⁻ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖w t ξ k‖ₑ ^ 2 :=
    fun t ht k => Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le (hwm t k)
      (hwint t ht k)
  have hUc : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Continuous (𝓕⁻ (fun ξ => w t ξ k)) :=
    fun t ht k => Navier.Analysis.WienerSmoothPath.continuous_fourierInv (hwint t ht k)
  have hUint : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3,
      Integrable (fun y => ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral (hUc t ht k)
      (ne_top_of_le_ne_top (hLw t ht k) (hPl t ht k))
  have hwsq : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Fin 3, Integrable (fun ξ => ‖w t ξ k‖ ^ 2) :=
    fun t ht k => integrable_norm_sq_of_lintegral' (hwm t k).aestronglyMeasurable (hLw t ht k)
  set c : ℝ := 1 / (2 * Real.pi) with hc
  have hbound : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x : Space =>
      c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2) := fun t ht =>
    integrable_space_euclid (g := fun y => c ^ 2 * ∑ k : Fin 3,
      ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2)
      ((integrable_finsetSum _ fun k _ => hUint t ht k).const_mul _)
  refine ⟨T, hT, physU w, physP w, hinit, ⟨⟨smoothVelocityBefore_physU hsm,
    Navier.Analysis.WienerPressureSmooth.smoothPressureBefore_physP hT hν a hfix hG,
    incompressibleBefore_physU hT hν a hfix hG ha,
    satisfiesNavierStokesBefore_physU hT hν a hfix hG rfl ha hreal⟩, ?_, ?_⟩⟩
  · -- finite energy
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hcont : Continuous (fun x : Space => physU w t x) := by
      refine continuous_pi fun k => ?_
      exact continuous_const.mul (Complex.continuous_re.comp ((hUc t ht k).comp
        (PiLp.continuous_toLp 2 _)))
    refine (hbound t ht).mono' ((continuous_norm.comp hcont).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (sq_norm_le_sum _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => physU_sq_le w t x k
  · -- energy inequality
    intro t ht0 htT
    have ht : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
    have hKt : kineticEnergy (physU w) t =
        c ^ 2 * ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 := by
      unfold kineticEnergy
      have hpt : ∀ x : Space, ∑ i : Fin 3, (physU w t x i) ^ 2 =
          c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)‖ ^ 2 := by
        intro x
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => physU_sq_eq w t x k ?_
        exact Complex.conj_eq_iff_im.mp (hreal t ht k (euclidPoint x))
      simp_rw [hpt]
      rw [integral_space_euclid (fun y => c ^ 2 * ∑ k : Fin 3, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2),
        integral_const_mul, integral_finsetSum _ fun k _ => hUint t ht k]
    have hK0 : kineticEnergy (physU w) 0 = ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      unfold kineticEnergy
      simp_rw [hinit]
    have hEW : ∀ s ∈ Icc (0 : ℝ) T, Navier.Analysis.WienerEnergy.EW w s =
        ∑ k : Fin 3, ∫ ξ, ‖w s ξ k‖ ^ 2 := by
      intro s hs
      unfold Navier.Analysis.WienerEnergy.EW Navier.Analysis.WienerEnergy.eW
      exact integral_finsetSum _ fun k _ => hwsq s hs k
    have hE := Navier.Analysis.WienerEnergy.energy_antitone hT hν a hfix hG hR0 hRb hsym ha ht
    rw [hEW t ht, hEW 0 ⟨le_rfl, hT.le⟩] at hE
    have hdat : ∑ k : Fin 3, ∫ ξ, ‖w 0 ξ k‖ ^ 2 =
        (2 * Real.pi) ^ 2 * ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      simp_rw [hw0]
      rw [hadef, fourierDatum_energy_eq_physical v₀, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hv₀, smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hle : ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2 ≤
        ∑ k : Fin 3, ∫ ξ, ‖w t ξ k‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => integral_sq_le_of_lintegral (hUint t ht k) (hwsq t ht k)
        (hPl t ht k)
    rw [hKt, hK0]
    have hc2 : c ^ 2 * (2 * Real.pi) ^ 2 = 1 := by rw [hc]; field_simp
    calc c ^ 2 * ∑ k : Fin 3, ∫ y, ‖𝓕⁻ (fun ξ => w t ξ k) y‖ ^ 2
        ≤ c ^ 2 * ∑ k : Fin 3, ∫ ξ, ‖w 0 ξ k‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (hle.trans hE) (by positivity)
      _ = ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
          rw [hdat, ← mul_assoc, hc2, one_mul]

/-- **Local classical existence at every positive viscosity.** -/
theorem localClassicalExistence :
    Navier.Analysis.CriticalControlDecomposition.LocalClassicalExistence :=
  Navier.Analysis.LocalExistenceViscosityReduction.localClassicalExistence_iff_atViscosityOne.mpr
    localClassicalExistenceAtViscosityOne

/-- **The crown, reduced to its two remaining inputs**: uniform BKM vorticity control at
viscosity one and the datum-horizon-independent BKM restart. -/
theorem wholeSpaceGlobalRegularity_of_bkmAtOne_datumRestart
    (hbkm : Navier.Analysis.LocalExistenceViscosityReduction.NSBKMUniformVorticityAprioriAtViscosityOne)
    (hrestart : Navier.Analysis.RestartPaste.DatumHorizonIndependentRestart
      Navier.Analysis.AprioriCriticalControlQuantifiers.bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  Navier.Analysis.ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart
    localClassicalExistenceAtViscosityOne hbkm hrestart

end Navier.Analysis.WienerLocalClassical

set_option pp.fullNames true in
#check @Navier.Analysis.WienerLocalClassical.localClassicalExistenceAtViscosityOne
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalClassical.localClassicalExistenceAtViscosityOne
set_option pp.fullNames true in
#check @Navier.Analysis.WienerLocalClassical.wholeSpaceGlobalRegularity_of_bkmAtOne_datumRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalClassical.wholeSpaceGlobalRegularity_of_bkmAtOne_datumRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalClassical.localClassicalExistence
