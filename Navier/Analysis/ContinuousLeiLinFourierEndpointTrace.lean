import Navier.Analysis.ContinuousLeiLinPhysicalVelocity
import Navier.Analysis.ContinuousLeiLinSelfMap
import Navier.Analysis.ContinuousLeiLinRecentTailJoint
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open Navier.Analysis.ContinuousLeiLinSpace Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity Navier.Analysis.ContinuousLeiLinPhysicalCarrier
namespace Navier.Analysis.FourierEndpointTrace
private def kernel (ν t : ℝ) (p : ES × ℝ) : ℂ :=
  if p.2 ≤ t then (Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2))) : ℂ) else 0

private theorem kernel_bound {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) (p : ES × ℝ) :
    ‖kernel ν t p‖ ≤ 1 := by
  unfold kernel
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg hν (sq_nonneg _)) (sub_nonneg.mpr h)))
  · simp

private theorem kernel_cont {t₀ : ℝ} (ν : ℝ) (p : ES × ℝ) (hp : p.2 ≠ t₀) :
    ContinuousAt (fun t => kernel ν t p) t₀ := by
  rcases lt_or_gt_of_ne hp with h | h
  · apply ContinuousAt.congr_of_eventuallyEq (f := fun t : ℝ => (Real.exp (-(ν * ‖p.1‖ ^ 2 * (t - p.2))) : ℂ)) (by fun_prop)
    filter_upwards [lt_mem_nhds h] with t ht
    simp [kernel, ht.le]
  · apply ContinuousAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℂ)) continuousAt_const
    filter_upwards [gt_mem_nhds h] with t ht
    simp [kernel, not_le.mpr ht]

private theorem duhamel_as_kernel (ν T t : ℝ) (ht : t ∈ Icc 0 T)
    (u v : ℝ → ES → ComplexSpace) (i : Fin 3) (ξ : ES) :
    continuousDuhamel ν u v t ξ i = ∫ s, kernel ν t (ξ,s) * continuousNavierSource u v s ξ i
      ∂(volume.restrict (Icc 0 T)) := by
  change (∫ s in Icc (0:ℝ) t, heatMode ν (t-s) (fun ζ => continuousNavierSource u v s ζ i) ξ) = _
  rw [show volume.restrict (Icc (0:ℝ) t) = (volume.restrict (Icc 0 T)).restrict (Icc 0 t)
    from (Measure.restrict_restrict_of_subset (Icc_subset_Icc_right ht.2)).symm]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (0:ℝ)) (b := T))] with s hs
  by_cases h : s ≤ t
  · simp [indicator_of_mem (show s ∈ Icc (0:ℝ) t from ⟨hs.1,h⟩),kernel,h,heatMode]
  · simp [kernel,h]

/-- An integrable spacetime Fourier source produces a canonical strongly continuous
Duhamel time section in the unweighted Fourier L¹ norm on the closed horizon. -/
theorem duhamel_strong_X0 {ν T : ℝ} (hν : 0 ≤ ν) (u v : ℝ → ES → ComplexSpace)
    (i : Fin 3) (hS : Integrable (fun p : ES × ℝ => continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0:ℝ) T)))) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc 0 T) :
    (∀ t ∈ Icc (0:ℝ) T, Integrable (fun ξ : ES => continuousDuhamel ν u v t ξ i)) ∧
    Tendsto (fun t : ℝ => ∫ ξ : ES, ‖continuousDuhamel ν u v t ξ i - continuousDuhamel ν u v t₀ ξ i‖)
      (𝓝[Icc 0 T] t₀) (𝓝 0) := by
  let μ := volume.restrict (Icc (0:ℝ) T)
  let Λ : Measure (ES × ℝ) := volume.prod μ
  let S := fun p : ES × ℝ => continuousNavierSource u v p.2 p.1 i
  let K := fun t p => kernel ν t p * S p
  have hS' : Integrable S Λ := hS
  have hKbound (t : ℝ) (p : ES × ℝ) : ‖K t p‖ ≤ ‖S p‖ := by
    dsimp [K]; rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (kernel_bound hν t p)
  have hK (t : ℝ) : Integrable (K t) Λ := by
    have hm : Measurable (kernel ν t) := by
      unfold kernel
      apply Measurable.ite (measurableSet_le measurable_snd measurable_const) <;> fun_prop
    exact hS'.norm.mono' (hm.aestronglyMeasurable.mul hS'.aestronglyMeasurable) (Eventually.of_forall (hKbound t))
  constructor
  · intro t ht
    exact (hK t).integral_prod_left.congr (ae_of_all _ fun ξ => (duhamel_as_kernel ν T t ht u v i ξ).symm)
  have hdiff (t : ℝ) := (hK t).sub (hK t₀)
  have hlim : Tendsto (fun t : ℝ => ∫ p, ‖K t p - K t₀ p‖ ∂Λ) (𝓝[Icc 0 T] t₀) (𝓝 0) := by
    have hne : ∀ᵐ p ∂Λ, p.2 ≠ t₀ :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ES)) (ν := μ)).tendsto_ae (μ.ae_ne t₀)
    simpa using tendsto_integral_filter_of_dominated_convergence
      (μ := Λ) (f := fun _ => (0 : ℝ)) (F := fun t p => ‖K t p - K t₀ p‖)
      (fun p => ‖S p‖ + ‖S p‖)
      (Eventually.of_forall fun t => (hdiff t).norm.aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (add_le_add (hKbound _ _) (hKbound _ _)))
      (hS'.norm.add hS'.norm)
      (hne.mono fun p hp => by
        have hc : ContinuousAt (fun t => K t p) t₀ := (kernel_cont ν p hp).mul continuousAt_const
        simpa using (hc.tendsto.sub (tendsto_const_nhds (x := K t₀ p))).norm.mono_left
          (nhdsWithin_le_nhds : 𝓝[Icc (0:ℝ) T] t₀ ≤ 𝓝 t₀))
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hi : Integrable (fun p : ES × ℝ => ‖K t p - K t₀ p‖) (volume.prod μ) := (hdiff t).norm
  change _ ≤ ∫ p : ES × ℝ, ‖K t p - K t₀ p‖ ∂(volume.prod μ)
  rw [integral_prod _ hi]
  have hrewrite (s : ℝ) (hs : s ∈ Icc 0 T) (ξ : ES) :
      continuousDuhamel ν u v s ξ i = ∫ σ, K s (ξ,σ) ∂μ := duhamel_as_kernel ν T s hs u v i ξ
  simp only [hrewrite t ht, hrewrite t₀ ht₀]
  apply integral_mono_ae
    ((hK t).integral_prod_left.sub (hK t₀).integral_prod_left).norm
    (hdiff t).norm.integral_prod_left
  filter_upwards [(hK t).prod_right_ae,(hK t₀).prod_right_ae] with ξ h1 h2
  simp only [Pi.sub_apply]
  rw [← integral_sub h1 h2]
  exact norm_integral_le_integral_norm _
#print axioms duhamel_strong_X0

/-- On an interval with a jointly integrable unweighted nonlinear source, the
actual mild image is strongly continuous in the Fourier Wiener norm. -/
theorem mild_strong_X0 {ν T : ℝ} (hν : 0 < ν) (a : ES → ComplexSpace)
    (v : ℝ → ES → ComplexSpace) (i : Fin 3) (ha : Integrable (fun ξ : ES => a ξ i))
    (hS : Integrable (fun p : ES × ℝ => continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0:ℝ) T)))) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc 0 T) :
    (∀ t ∈ Icc (0:ℝ) T, Integrable (fun ξ : ES => continuousMildImage ν hν a v t ξ i)) ∧
    Tendsto (fun t : ℝ => ∫ ξ : ES,
      ‖continuousMildImage ν hν a v t ξ i - continuousMildImage ν hν a v t₀ ξ i‖)
      (𝓝[Icc 0 T] t₀) (𝓝 0) := by
  let H := fun t (ξ : ES) => heatVec ν t a ξ i
  let D := fun t (ξ : ES) => continuousDuhamel ν v v t ξ i
  obtain ⟨hDi,hDc⟩ := duhamel_strong_X0 hν.le v v i hS t₀ ht₀
  have hHm (t : ℝ) : AEStronglyMeasurable (H t) volume := by
    have hc : Continuous (fun ξ : ES => (Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℂ)) := by fun_prop
    exact hc.aestronglyMeasurable.mul ha.aestronglyMeasurable
  have hHb (t : ℝ) (ht : 0 ≤ t) (ξ : ES) : ‖H t ξ‖ ≤ ‖a ξ i‖ := by
    change ‖(Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℂ) * a ξ i‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (mul_nonneg hν.le (sq_nonneg _)) ht)))
  have hHi (t : ℝ) (ht : 0 ≤ t) : Integrable (H t) :=
    ha.norm.mono' (hHm t) (ae_of_all _ (hHb t ht))
  constructor
  · intro t ht
    exact (hHi t ht.1).add (hDi t ht)
  have hHc : Tendsto (fun t : ℝ => ∫ ξ : ES, ‖H t ξ - H t₀ ξ‖) (𝓝[Icc 0 T] t₀) (𝓝 0) := by
    suffices hc : Tendsto (fun t : ℝ => ∫ ξ : ES, ‖H t ξ - H t₀ ξ‖) (𝓝[Icc 0 T] t₀) (𝓝 (∫ _ : ES, (0 : ℝ))) by simpa using hc
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ : ES => ‖a ξ i‖ + ‖a ξ i‖)
    · exact Eventually.of_forall fun t => ((hHm t).sub (hHm t₀)).norm
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ae_of_all _ fun ξ => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (add_le_add (hHb t ht.1 ξ) (hHb _ ht₀.1 ξ))
    · exact ha.norm.add ha.norm
    · refine ae_of_all _ fun ξ => ?_
      have hc : Continuous (fun t : ℝ => H t ξ) := by dsimp [H,heatVec,heatMode]; fun_prop
      simpa using ((hc.tendsto t₀).sub (tendsto_const_nhds (x := H t₀ ξ))).norm.mono_left
        (nhdsWithin_le_nhds : 𝓝[Icc (0:ℝ) T] t₀ ≤ 𝓝 t₀)
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _
    (by simpa using hHc.add hDc)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hHi' : Integrable (fun ξ : ES => ‖H t ξ - H t₀ ξ‖) := ((hHi t ht.1).sub (hHi _ ht₀.1)).norm
  have hDi' : Integrable (fun ξ : ES => ‖D t ξ - D t₀ ξ‖) := ((hDi t ht).sub (hDi _ ht₀)).norm
  change (∫ ξ : ES, ‖(H t ξ + D t ξ) - (H t₀ ξ + D t₀ ξ)‖) ≤
    (∫ ξ : ES, ‖H t ξ - H t₀ ξ‖) + (∫ ξ : ES, ‖D t ξ - D t₀ ξ‖)
  rw [← integral_add hHi' hDi']
  refine integral_mono (((hHi t ht.1).add (hDi t ht)).sub ((hHi _ ht₀.1).add (hDi _ ht₀))).norm
    (hHi'.add hDi') (fun ξ => ?_)
  change ‖(H t ξ + D t ξ) - (H t₀ ξ + D t₀ ξ)‖ ≤ ‖H t ξ - H t₀ ξ‖ + ‖D t ξ - D t₀ ξ‖
  rw [show H t ξ + D t ξ - (H t₀ ξ + D t₀ ξ) = (H t ξ - H t₀ ξ) + (D t ξ - D t₀ ξ) by abel]
  exact norm_add_le _ _
#print axioms mild_strong_X0



open Navier.Analysis.ContinuousLeiLinRecentTailJoint Navier.Analysis.ComplexLerayNorm
/-- The project's zeroth-order nonlinear moment estimate supplies the required
complex source integrability from the input fields and their first moments. -/
theorem integrable_source_of_input_moments (u v : ℝ → ES → ComplexSpace) (T : ℝ) (i : Fin 3)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc (0:ℝ) T))))
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hv : ∀ s i, AEStronglyMeasurable (fun η : ES => v s η i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (huN : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ (1 : ℕ) * ‖u s η j‖))
    (hvN : ∀ s i, Integrable (fun η : ES => ‖η‖ ^ (1 : ℕ) * ‖v s η i‖))
    (hmajor : Integrable (fun s => sourceMomentMajorant 0 (u s) (v s))
      (volume.restrict (Icc (0:ℝ) T))) :
    Integrable (fun p : ES × ℝ => continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0:ℝ) T))) := by
  have hm := continuousNavierSource_coord_aestronglyMeasurable u v 0 T hjoint i
  apply (integrable_norm_iff hm).mp
  simpa using integrable_joint_pow_norm_continuousNavierSource_coord 0 u v 0 T i
    hjoint hu hv hu0 hv0 huN hvN hmajor
#print axioms integrable_source_of_input_moments
theorem mild_initial_trace (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace) :
    continuousMildImage ν hν a u 0 = a := by
  funext ξ i
  simp [continuousMildImage_coord_apply, continuousDuhamel, heatVec, heatMode]
theorem physical_initial_trace (ν : ℝ) (hν : 0 < ν) (a : Navier.SchwartzVelocity)
    (u : ℝ → ES → ComplexSpace) (x : Navier.Space) (i : Fin 3) :
    physicalVelocity (continuousMildImage ν hν (fourierDatum a) u) 0 x i = a x i :=
  physicalVelocity_fourierDatum a _ 0 (mild_initial_trace ν hν _ u) x i
#print axioms mild_initial_trace
#print axioms physical_initial_trace


/-- Strong continuity in the exact three-coordinate norm used by the original
physical-velocity and bilinear estimates. -/
theorem mild_coordinateX0_trace {ν T : ℝ} (hν : 0 < ν) (a : ES → ComplexSpace)
    (v : ℝ → ES → ComplexSpace) (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => a ξ i))
    (hS : ∀ i : Fin 3, Integrable (fun p : ES × ℝ => continuousNavierSource v v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0:ℝ) T)))) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc 0 T) :
    Tendsto (fun t : ℝ => coordinateX0Mass (fun ξ =>
      continuousMildImage ν hν a v t ξ - continuousMildImage ν hν a v t₀ ξ))
      (𝓝[Icc 0 T] t₀) (𝓝 0) := by
  simpa [coordinateX0Mass] using tendsto_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => (mild_strong_X0 hν a v i (ha i) (hS i) t₀ ht₀).2)
#print axioms mild_coordinateX0_trace
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalVelocity.physicalVelocity_fourierDatum
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource_coord
end Navier.Analysis.FourierEndpointTrace
