import Navier.Analysis.WienerLocalMild
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

/-!
# From the Wiener-carrier fixed point to the pointwise continuous mild map

Bridge from `WienerLocalMild.exists_wienerMildSolution` (a fixed point in
coefficient classes, `C([0,T], L¹(ℝ³;ℂ)³)`) to the pointwise continuous mild
map `ContinuousLeiLinSelfMap.continuousMildImage` used by the repository's
physical-velocity lift.

This first part proves the evaluation principle for `L¹`-valued Bochner
integrals: if a jointly integrable kernel `g(σ, ξ)` represents `G σ` for a.e.
`σ`, then `∫ G` is represented by `ξ ↦ ∫ g(σ, ξ) dσ`
(`integral_L1C_ae_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Convolution

namespace Navier.Analysis.WienerPointwiseBridge

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinRepresentativeInvariant

/-! ## Set integrals as continuous functionals on `L¹` -/

theorem setIntegral_add_L1C (E : Set ES) (f g : L1C) :
    ∫ ξ in E, (f + g : L1C) ξ = (∫ ξ in E, f ξ) + ∫ ξ in E, g ξ := by
  rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
  exact integral_add (L1.integrable_coeFn f).integrableOn (L1.integrable_coeFn g).integrableOn

theorem setIntegral_smul_L1C (E : Set ES) (c : ℂ) (f : L1C) :
    ∫ ξ in E, (c • f : L1C) ξ = c • ∫ ξ in E, f ξ := by
  rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
  exact integral_smul c _

theorem norm_setIntegral_L1C_le (E : Set ES) (f : L1C) :
    ‖∫ ξ in E, f ξ‖ ≤ ‖f‖ := by
  rw [L1.norm_eq_integral_norm]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (L1.integrable_coeFn f).norm
      (Eventually.of_forall fun _ => norm_nonneg _))

/-- `f ↦ ∫_E f` on `L¹(ℝ³; ℂ)`. -/
def setIntCLM (E : Set ES) : L1C →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ ξ in E, f ξ
      map_add' := setIntegral_add_L1C E
      map_smul' := setIntegral_smul_L1C E } 1
    (fun f => by simpa [one_mul] using norm_setIntegral_L1C_le E f)

theorem setIntCLM_apply (E : Set ES) (f : L1C) : setIntCLM E f = ∫ ξ in E, f ξ := rfl

/-! ## Evaluation of `L¹`-valued Bochner integrals -/

/-- **Evaluation principle.**  If `g` is integrable on `S × ℝ³` and represents
`G σ` for a.e. `σ ∈ S`, the Bochner integral `∫_S G` is represented by the
pointwise integral `ξ ↦ ∫_S g(σ, ξ) dσ`. -/
theorem integral_L1C_ae_eq {S : Set ℝ} (G : ℝ → L1C)
    (hG : Integrable G (volume.restrict S)) (g : ℝ → ES → ℂ)
    (hg : Integrable (Function.uncurry g) ((volume.restrict S).prod volume))
    (hgG : ∀ᵐ σ ∂(volume.restrict S), g σ =ᵐ[volume] G σ) :
    ⇑(∫ σ in S, G σ : L1C) =ᵐ[volume] fun ξ => ∫ σ in S, g σ ξ := by
  have hH : Integrable (fun ξ => ∫ σ in S, g σ ξ) volume :=
    Integrable.integral_prod_right (μ := volume.restrict S) (ν := (volume : Measure ES))
      (f := Function.uncurry g) hg
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) hH ?_
  intro E hE _hEfin
  have hgE : Integrable (Function.uncurry g) ((volume.restrict S).prod (volume.restrict E)) := by
    have hrw : (volume.restrict S).prod (volume.restrict E) =
        (((volume : Measure ℝ).restrict S).prod (volume : Measure ES)).restrict (univ ×ˢ E) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hrw]
    exact hg.restrict
  calc ∫ ξ in E, (∫ σ in S, G σ : L1C) ξ = setIntCLM E (∫ σ in S, G σ) := rfl
    _ = ∫ σ in S, setIntCLM E (G σ) := ((setIntCLM E).integral_comp_comm hG).symm
    _ = ∫ σ in S, ∫ ξ in E, g σ ξ := by
        refine integral_congr_ae ?_
        filter_upwards [hgG] with σ hσ
        rw [setIntCLM_apply]
        exact (integral_congr_ae (ae_restrict_of_ae hσ)).symm
    _ = ∫ ξ in E, ∫ σ in S, g σ ξ := integral_integral_swap hgE

/-! ## Finite sums of `Lp` classes -/

theorem coeFn_finset_sum_Lp {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι)
    (f : ι → Lp E 1 (volume : Measure ES)) :
    ⇑(∑ i ∈ s, f i) =ᵐ[volume] ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero E 1 (volume : Measure ES)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ξ h1 h2
      rw [h1, Pi.add_apply, Pi.add_apply, h2]

/-! ## The vector-valued `L¹` embedding and a joint representative -/

/-- Coordinate injection `ℂ → PiLp 1 ℂ³`. -/
def coordInj (i : Fin 3) : ℂ →L[ℂ] FourierCoordinateL1 :=
  (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin 3 => ℂ) i)

/-- Three scalar `L¹` coordinates as one vector-valued `L¹` class. -/
def iota : V1 →L[ℂ] Lp FourierCoordinateL1 1 (volume : Measure ES) :=
  ∑ i : Fin 3, ((coordInj i).compLpL 1 (volume : Measure ES)).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i)

theorem coeFn_iota (v : V1) :
    iota v =ᵐ[volume] fun ξ => (WithLp.toLp 1 (fun i => v i ξ) : FourierCoordinateL1) := by
  have hsum : iota v = ∑ i : Fin 3, (coordInj i).compLpL 1 (volume : Measure ES) (v i) := by
    simp [iota]
  have hcoe : ∀ i : Fin 3, ⇑((coordInj i).compLpL 1 (volume : Measure ES) (v i)) =ᵐ[volume]
      fun ξ => coordInj i (v i ξ) := fun i =>
    (coordInj i).coeFn_compLpL (v i)
  rw [hsum]
  filter_upwards [coeFn_finset_sum_Lp Finset.univ
      (fun i : Fin 3 => (coordInj i).compLpL 1 (volume : Measure ES) (v i)),
    hcoe 0, hcoe 1, hcoe 2] with ξ h h0 h1 h2
  rw [h, Finset.sum_apply, Fin.sum_univ_three, h0, h1, h2]
  ext j
  fin_cases j <;> simp [coordInj]

variable {ν T : ℝ}

/-- **A jointly measurable representative of a Wiener-carrier path**, whose
time sections represent the path for a.e. time on the horizon. -/
theorem exists_joint_rep (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, V1)) :
    ∃ v : ℝ → ES → ComplexSpace,
      (∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i)) ∧
      ∀ᵐ s ∂leiLinTimeMeasure T, ∀ i : Fin 3,
        (fun ξ => v s ξ i) =ᵐ[volume] ⇑(extend hT x s i) := by
  set P : ℝ → Lp FourierCoordinateL1 1 (volume : Measure ES) :=
    fun s => iota (extend hT x s) with hP
  have hPc : Continuous P := iota.continuous.comp (continuous_extend hT x)
  have hPm : MemLp P 1 (leiLinTimeMeasure T) :=
    MemLp.of_bound hPc.aestronglyMeasurable (‖iota‖ * ‖x‖)
      (Eventually.of_forall fun s => (iota.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_extend_le hT x s) (norm_nonneg _)))
  obtain ⟨u, hu, hut⟩ := exists_stronglyMeasurable_jointVersion (volume : Measure ES)
    (leiLinTimeMeasure T) inferInstance inferInstance (hPm.toLp P)
  refine ⟨fun s ξ i => WithLp.ofLp (u (ξ, s)) i, fun i => ?_, ?_⟩
  · exact ((continuous_apply i).comp (PiLp.continuous_ofLp 1 _)).comp_stronglyMeasurable hu
  · filter_upwards [hut, hPm.coeFn_toLp] with s h1 h2 i
    rw [h2] at h1
    filter_upwards [h1, coeFn_iota (extend hT x s)] with ξ h3 h4
    change WithLp.ofLp (u (ξ, s)) i = _
    rw [h3, h4]

/-! ## The pointwise Duhamel kernel -/

/-- Kernel form of the heat-weighted Navier symbol. -/
theorem heat_mul_bilinear_eq (ν σ : ℝ) (a : ES → ComplexSpace) (ξ : ES) (i : Fin 3) :
    (heatFactor ν σ ξ : ℂ) * continuousNavierBilinear a a ξ i =
      ∑ j : Fin 3, ∑ k : Fin 3, kernelSymbol ν σ i j k ξ *
        ((fun η => a η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => a η k)) ξ := by
  have h := sum_lerayDerivSymbol ξ
    (fun j k => ((fun η => a η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => a η k)) ξ) i
  unfold continuousNavierBilinear rawNavierConvection
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold kernelSymbol
  ring

/-- The pointwise σ-integrand at time `t`, coordinate `i`. -/
def gDuh (ν : ℝ) (v : ℝ → ES → ComplexSpace) (t : ℝ) (i : Fin 3) (σ : ℝ) (ξ : ES) : ℂ :=
  (Iic t).indicator
    (fun σ => (heatFactor ν σ ξ : ℂ) * continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ i) σ

/-- Change of variables `s = t - σ`: the cut integrand integrates to the
repository's pointwise causal Duhamel term. -/
theorem integral_gDuh_eq (ν : ℝ) (v : ℝ → ES → ComplexSpace) {t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (i : Fin 3) (ξ : ES) :
    ∫ σ in Ioc 0 T, gDuh ν v t i σ ξ = continuousDuhamel ν v v t ξ i := by
  unfold gDuh
  rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right htT]
  set φ : ℝ → ℂ := fun s =>
    ((Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) : ℝ) : ℂ) *
      continuousNavierBilinear (v s) (v s) ξ i with hφ
  have hfun : (fun σ => (heatFactor ν σ ξ : ℂ) *
      continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ i) = fun σ => φ (t - σ) := by
    funext σ
    simp only [hφ, heatFactor, sub_sub_cancel]
  rw [hfun, ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_comp_sub_left,
    sub_self, sub_zero, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  unfold continuousDuhamel
  simp only [hφ, heatMode, continuousNavierSource]

/-! ## Representation of the class-level integrand -/

theorem gDuh_of_le (ν : ℝ) (v : ℝ → ES → ComplexSpace) {t σ : ℝ} (hle : σ ≤ t)
    (i : Fin 3) (ξ : ES) :
    gDuh ν v t i σ ξ = ∑ j : Fin 3, ∑ k : Fin 3, kernelSymbol ν σ i j k ξ *
      ((fun η => v (t - σ) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => v (t - σ) η k)) ξ := by
  have h : gDuh ν v t i σ ξ =
      (heatFactor ν σ ξ : ℂ) * continuousNavierBilinear (v (t - σ)) (v (t - σ)) ξ i := by
    unfold gDuh
    exact indicator_of_mem (show σ ∈ Iic t from hle) _
  rw [h]
  exact heat_mul_bilinear_eq ν σ (v (t - σ)) ξ i

theorem duhIntegrand_coord_of_le (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, V1)) {t σ : ℝ}
    (hle : σ ≤ t) (i : Fin 3) :
    duhIntegrand ν hT x x t σ i = ∑ j : Fin 3, ∑ k : Fin 3,
      mulL (kernelLinf ν σ i j k)
        (conv (extend hT x (t - σ) j) (extend hT x (t - σ) k)) := by
  have h : duhIntegrand ν hT x x t σ =
      kernelOp ν σ (tensorConv (extend hT x (t - σ)) (extend hT x (t - σ))) := by
    unfold duhIntegrand
    exact indicator_of_mem (show σ ∈ Iic t from hle) _
  rw [h, kernelOp, tensorMulOp_apply]
  simp only [tensorConv_apply]

theorem coeFn_double_sum (m : Fin 3 → Fin 3 → L1C) (M : Fin 3 → Fin 3 → ES → ℂ)
    (h : ∀ j k, ⇑(m j k) =ᵐ[volume] M j k) :
    ⇑(∑ j : Fin 3, ∑ k : Fin 3, m j k) =ᵐ[volume]
      fun ξ => ∑ j : Fin 3, ∑ k : Fin 3, M j k ξ := by
  have houter := coeFn_finset_sum_Lp Finset.univ (fun j : Fin 3 => ∑ k : Fin 3, m j k)
  have hinner : ∀ j : Fin 3, ⇑(∑ k : Fin 3, m j k) =ᵐ[volume] ∑ k : Fin 3, ⇑(m j k) :=
    fun j => coeFn_finset_sum_Lp Finset.univ _
  filter_upwards [houter, ae_all_iff.mpr hinner,
    ae_all_iff.mpr fun j => ae_all_iff.mpr (h j)] with ξ h1 h2 h3
  rw [h1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 j, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => h3 j k

theorem gDuh_ae_eq (hν : 0 < ν) (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, V1))
    (v : ℝ → ES → ComplexSpace) {t σ : ℝ} (hσ : 0 < σ)
    (hrep : σ ≤ t → ∀ i : Fin 3,
      (fun ξ => v (t - σ) ξ i) =ᵐ[volume] ⇑(extend hT x (t - σ) i)) (i : Fin 3) :
    (fun ξ => gDuh ν v t i σ ξ) =ᵐ[volume] ⇑(duhIntegrand ν hT x x t σ i) := by
  by_cases hle : σ ≤ t
  · rw [duhIntegrand_coord_of_le hT x hle i]
    have hr := hrep hle
    have hterm : ∀ j k : Fin 3,
        ⇑(mulL (kernelLinf ν σ i j k)
          (conv (extend hT x (t - σ) j) (extend hT x (t - σ) k))) =ᵐ[volume] fun ξ =>
          kernelSymbol ν σ i j k ξ *
            ((fun η => v (t - σ) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => v (t - σ) η k)) ξ := by
      intro j k
      have hconv : (⇑(extend hT x (t - σ) j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            ⇑(extend hT x (t - σ) k)) =
          (fun η => v (t - σ) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => v (t - σ) η k) :=
        convolution_congr _ (hr j).symm (hr k).symm
      filter_upwards [coeFn_mulL (kernelLinf ν σ i j k)
          (conv (extend hT x (t - σ) j) (extend hT x (t - σ) k)),
        coeFn_kernelLinf hν hσ i j k,
        coeFn_convFun (extend hT x (t - σ) j) (extend hT x (t - σ) k)] with ξ h1 h2 h3
      rw [h1, h2, conv_apply, h3, hconv]
    filter_upwards [coeFn_double_sum _ _ hterm] with ξ h
    rw [h, gDuh_of_le ν v hle i ξ]
  · have h0 : duhIntegrand ν hT x x t σ = 0 := by
      unfold duhIntegrand
      exact indicator_of_notMem (show σ ∉ Iic t from hle) _
    have hg0 : ∀ ξ, gDuh ν v t i σ ξ = 0 := fun ξ => by
      unfold gDuh
      exact indicator_of_notMem (show σ ∉ Iic t from hle) _
    rw [h0]
    filter_upwards [Lp.coeFn_zero ℂ 1 (volume : Measure ES)] with ξ h
    rw [hg0, Pi.zero_apply, h]
    rfl

theorem stronglyMeasurable_gDuh (ν : ℝ) (v : ℝ → ES → ComplexSpace)
    (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i)) (t : ℝ)
    (i : Fin 3) : StronglyMeasurable (Function.uncurry (gDuh ν v t i)) := by
  have hC : ∀ j k : Fin 3, StronglyMeasurable (fun p : ℝ × ES =>
      ((fun η => v (t - p.1) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => v (t - p.1) η k)) p.2) := by
    intro j k
    have hf : StronglyMeasurable (fun q : (ℝ × ES) × ES =>
        v (t - q.1.1) q.2 j * v (t - q.1.1) (q.1.2 - q.2) k) := by
      have m1 : Measurable (fun q : (ℝ × ES) × ES => (q.2, t - q.1.1)) :=
        measurable_snd.prodMk (measurable_const.sub (measurable_fst.comp measurable_fst))
      have m2 : Measurable (fun q : (ℝ × ES) × ES => (q.1.2 - q.2, t - q.1.1)) :=
        ((measurable_snd.comp measurable_fst).sub measurable_snd).prodMk
          (measurable_const.sub (measurable_fst.comp measurable_fst))
      exact ((hvm j).comp_measurable m1).mul ((hvm k).comp_measurable m2)
    have := hf.integral_prod_right' (ν := (volume : Measure ES))
    have heq : (fun p : ℝ × ES =>
        ((fun η => v (t - p.1) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η => v (t - p.1) η k)) p.2) =
        fun p : ℝ × ES => ∫ η, v (t - p.1) η j * v (t - p.1) (p.2 - η) k := by
      funext p
      simp [convolution_def]
    rw [heq]
    exact this
  have hK : ∀ j k : Fin 3, StronglyMeasurable (fun p : ℝ × ES => kernelSymbol ν p.1 i j k p.2) := by
    intro j k
    have hh : Continuous (fun p : ℝ × ES => (heatFactor ν p.1 p.2 : ℂ)) := by
      unfold heatFactor; fun_prop
    exact (hh.measurable.mul ((measurable_lerayDerivSymbol i j k).comp measurable_snd)).stronglyMeasurable
  have hsum : StronglyMeasurable (fun p : ℝ × ES => ∑ j : Fin 3, ∑ k : Fin 3,
      kernelSymbol ν p.1 i j k p.2 *
        ((fun η => v (t - p.1) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η => v (t - p.1) η k)) p.2) :=
    Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      Finset.stronglyMeasurable_fun_sum _ fun k _ => (hK j k).mul (hC j k)
  have hite : StronglyMeasurable (fun p : ℝ × ES =>
      if p.1 ≤ t then ∑ j : Fin 3, ∑ k : Fin 3, kernelSymbol ν p.1 i j k p.2 *
        ((fun η => v (t - p.1) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η => v (t - p.1) η k)) p.2 else 0) :=
    StronglyMeasurable.ite (measurableSet_le measurable_fst measurable_const) hsum
      stronglyMeasurable_const
  have heq : Function.uncurry (gDuh ν v t i) = fun p : ℝ × ES =>
      if p.1 ≤ t then ∑ j : Fin 3, ∑ k : Fin 3, kernelSymbol ν p.1 i j k p.2 *
        ((fun η => v (t - p.1) η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun η => v (t - p.1) η k)) p.2 else 0 := by
    funext p
    by_cases hp : p.1 ≤ t
    · rw [if_pos hp]; exact gDuh_of_le ν v hp i p.2
    · rw [if_neg hp]
      show gDuh ν v t i p.1 p.2 = 0
      unfold gDuh
      exact indicator_of_notMem (show p.1 ∉ Iic t from hp) _
  rw [heq]
  exact hite

/-- Transfer an a.e.-time statement on `[0,T]` to the reflected lag variable. -/
theorem ae_reflect {P : ℝ → Prop} (hP : ∀ᵐ s ∂leiLinTimeMeasure T, P s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∀ᵐ σ ∂(volume.restrict (Ioc (0 : ℝ) T)), σ ≤ t → P (t - σ) := by
  have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) T → P s :=
    (ae_restrict_iff' measurableSet_Icc).mp hP
  have h2 : ∀ᵐ σ ∂(volume : Measure ℝ), t - σ ∈ Icc (0 : ℝ) T → P (t - σ) :=
    ((volume : Measure ℝ).measurePreserving_sub_left t).quasiMeasurePreserving.ae h1
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [h2] with σ hσ hmem hle
  exact hσ ⟨by linarith, by linarith [hmem.1, ht.2]⟩

/-! ## Evaluation of the Duhamel term and the heat term -/

section Assembly

variable (hν : 0 < ν) (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, V1)) (v : ℝ → ES → ComplexSpace)
  (hvm : ∀ i : Fin 3, StronglyMeasurable (fun p : ES × ℝ => v p.2 p.1 i))
  (hv : ∀ᵐ s ∂leiLinTimeMeasure T, ∀ i : Fin 3,
    (fun ξ => v s ξ i) =ᵐ[volume] ⇑(extend hT x s i))
include hν hv

theorem ae_gDuh {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    ∀ᵐ σ ∂(volume.restrict (Ioc (0 : ℝ) T)),
      (fun ξ => gDuh ν v t i σ ξ) =ᵐ[volume] ⇑(duhIntegrand ν hT x x t σ i) := by
  filter_upwards [ae_reflect hv ht, ae_restrict_mem measurableSet_Ioc] with σ h hσ
  exact gDuh_ae_eq hν hT x v hσ.1 h i

include hvm in
theorem integrable_gDuh {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    Integrable (Function.uncurry (gDuh ν v t i))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod volume) := by
  have hae := ae_gDuh hν hT x v hv ht i
  rw [integrable_prod_iff (stronglyMeasurable_gDuh ν v hvm t i).aestronglyMeasurable]
  constructor
  · filter_upwards [hae] with σ h
    exact (L1.integrable_coeFn _).congr h.symm
  · have hN : Integrable (fun σ => ‖duhIntegrand ν hT x x t σ i‖)
        (volume.restrict (Ioc (0 : ℝ) T)) :=
      (integrable_duhIntegrand hν hT x x t).norm.mono'
        (((continuous_apply i).comp_aestronglyMeasurable
          (aestronglyMeasurable_duhIntegrand hν hT x x t)).norm)
        (Eventually.of_forall fun σ => by
          rw [norm_norm]; exact norm_le_pi_norm _ i)
    refine hN.congr ?_
    filter_upwards [hae] with σ h
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [h] with ξ hξ
    simp only [Function.uncurry_apply_pair]
    rw [hξ]

include hvm in
/-- **The class-level Duhamel term is represented by the repository's pointwise
causal Duhamel term.** -/
theorem duhamel_coord_ae_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    ⇑((duhamel ν hT x x t) i) =ᵐ[volume] fun ξ => continuousDuhamel ν v v t ξ i := by
  have hint := integrable_duhIntegrand hν hT x x t
  have hcoord : (duhamel ν hT x x t) i = ∫ σ in Ioc 0 T, duhIntegrand ν hT x x t σ i := by
    unfold duhamel
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integral_comp_comm
      hint).symm
  rw [hcoord]
  have hG : Integrable (fun σ => duhIntegrand ν hT x x t σ i)
      (volume.restrict (Ioc (0 : ℝ) T)) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integrable_comp hint
  filter_upwards [integral_L1C_ae_eq _ hG (gDuh ν v t i)
    (integrable_gDuh hν hT x v hvm hv ht i) (ae_gDuh hν hT x v hv ht i)] with ξ h
  rw [h, integral_gDuh_eq ν v ht.1 ht.2 i ξ]

end Assembly

theorem heatOp_coord_ae_eq (hν : 0 < ν) (a₀ : V1) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    ⇑(heatOp ν t a₀ i) =ᵐ[volume] fun ξ => heatVec ν t (fun ξ i => a₀ i ξ) ξ i := by
  rw [heatOp_apply]
  filter_upwards [coeFn_mulL (heatLinf ν t) (a₀ i), coeFn_heatLinf hν.le t] with ξ h1 h2
  rw [h1, h2, max_eq_left ht]
  rfl

/-! ## The consumed endpoint: a pointwise fixed point of `continuousMildImage` -/

/-- **Large-data local existence of a pointwise continuous mild fixed point.**
For every `ν > 0`, every Wiener datum `a₀ ∈ L¹(ℝ³;ℂ)³` and every horizon with
`10⁴ T ‖a₀‖² ≤ ν`, there is a Wiener-carrier path `x` with `‖x‖ ≤ 2‖a₀‖` and
a pointwise Fourier field `w` such that every time section of `w` represents
`x`, and `w` is a fixed point of the repository's pointwise mild map
`continuousMildImage` at EVERY time of `[0,T]` and EVERY frequency. -/
theorem exists_wienerMild_pointwise (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1), ‖x‖ ≤ 2 * ‖a₀‖ ∧ ∃ w : ℝ → ES → ComplexSpace,
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
        (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES,
        w t ξ = continuousMildImage ν hν (fun ξ i => a₀ i ξ) w t ξ := by
  obtain ⟨x, hxle, hxeq⟩ := exists_wienerMildSolution hν hT a₀ hsmall
  obtain ⟨v, hvm, hv⟩ := exists_joint_rep hT.le x
  set a₀' : ES → ComplexSpace := fun ξ i => a₀ i ξ with ha₀'
  set w : ℝ → ES → ComplexSpace := continuousMildImage ν hν a₀' v with hw
  have hext : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T), extend hT.le x t = x ⟨t, ht⟩ := by
    intro t ht
    unfold WienerLocalMild.extend
    rw [projIcc_of_mem hT.le ht]
  have key : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3),
      (fun ξ => w t ξ i) =ᵐ[volume] ⇑(x ⟨t, ht⟩ i) := by
    intro t ht i
    have hx := hxeq ⟨t, ht⟩
    rw [← duhamel_eq_causal hT.le x x ht.2] at hx
    rw [hx]
    filter_upwards [Lp.coeFn_add (heatOp ν t a₀ i) (duhamel ν hT.le x x t i),
      heatOp_coord_ae_eq hν a₀ ht.1 i,
      duhamel_coord_ae_eq hν hT.le x v hvm hv ht i] with ξ h1 h2 h3
    rw [Pi.add_apply, h1, Pi.add_apply, h2, h3]
    rfl
  refine ⟨x, hxle, w, key, fun t ht ξ => ?_⟩
  have huv : ∀ᵐ s ∂leiLinTimeMeasure T, w s =ᵐ[volume] v s := by
    filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with s hs hmem
    have hc : ∀ i : Fin 3, (fun ξ => w s ξ i) =ᵐ[volume] fun ξ => v s ξ i := fun i => by
      have h1 := key s hmem i
      have h2 := hs i
      rw [hext s hmem] at h2
      exact h1.trans h2.symm
    filter_upwards [ae_all_iff.mpr hc] with ξ h
    funext i
    exact h i
  rw [continuousMildImage_congr_ae_on_horizon ν hν T a₀' w v huv t ht ξ]

end Navier.Analysis.WienerPointwiseBridge

set_option pp.fullNames true in
#check @Navier.Analysis.WienerPointwiseBridge.exists_wienerMild_pointwise
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPointwiseBridge.exists_wienerMild_pointwise
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPointwiseBridge.integral_L1C_ae_eq
