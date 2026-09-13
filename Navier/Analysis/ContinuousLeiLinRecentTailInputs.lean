import Navier.Analysis.ContinuousLeiLinRecentTailJoint

set_option autoImplicit false

noncomputable section

open scoped Convolution

open MeasureTheory Set
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinRecentTailMoment
open Navier.Analysis.ContinuousLeiLinRecentTailJoint

namespace Navier.Analysis.ContinuousLeiLinRecentTailInputs

theorem convolution_joint_aestronglyMeasurable_of_continuous
    (f g : ℝ → ES → ℂ) (μ : Measure (ES × ℝ))
    (hf : Continuous (fun p : ES × ℝ => f p.2 p.1))
    (hg : Continuous (fun p : ES × ℝ => g p.2 p.1)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      ((fun η : ES => f p.2 η) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => g p.2 η)) p.1) μ := by
  have hInt : StronglyMeasurable (fun q : (ES × ℝ) × ES =>
      f q.1.2 q.2 * g q.1.2 (q.1.1 - q.2)) := by
    have hmapf : Continuous (fun q : (ES × ℝ) × ES => (q.2, q.1.2)) :=
      continuous_snd.prodMk (continuous_snd.comp continuous_fst)
    have hmapg : Continuous (fun q : (ES × ℝ) × ES =>
        (q.1.1 - q.2, q.1.2)) :=
      ((continuous_fst.comp continuous_fst).sub continuous_snd).prodMk
        (continuous_snd.comp continuous_fst)
    exact (hf.comp hmapf).stronglyMeasurable.mul (hg.comp hmapg).stronglyMeasurable
  exact hInt.integral_prod_right'.aestronglyMeasurable

/-- Joint continuity of the two frequency trajectories supplies the joint
Bochner measurability of their genuine Leray-projected Navier source. -/
theorem continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    (u v : ℝ → ES → ComplexSpace) (τ t : ℝ)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i)) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t))) := by
  let μ : Measure (ES × ℝ) := volume.prod (volume.restrict (Icc τ t))
  have hconv (i j : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      ((fun η : ES => u p.2 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => v p.2 η i)) p.1) μ :=
    convolution_joint_aestronglyMeasurable_of_continuous
      (fun s η => u s η j) (fun s η => v s η i) μ (hu j) (hv i)
  have hraw : AEStronglyMeasurable (fun p : ES × ℝ =>
      rawNavierConvection (u p.2) (v p.2) p.1) μ := by
    apply (aemeasurable_pi_lambda _ ?_).aestronglyMeasurable
    intro i
    change AEMeasurable (fun p : ES × ℝ => ∑ j : Fin 3, (p.1 j : ℂ) *
      ((fun η : ES => u p.2 η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => v p.2 η i)) p.1) μ
    exact (Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => by
      have hcoord : Continuous (fun p : ES × ℝ => (p.1 j : ℝ)) :=
        (PiLp.continuous_apply 2 _ j).comp continuous_fst
      exact ((Complex.continuous_ofReal.comp hcoord).aestronglyMeasurable).mul
        (hconv i j))).aemeasurable
  have hrawE : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)) μ :=
    (PiLp.continuous_toLp 2 _).aestronglyMeasurable.comp_aemeasurable hraw.aemeasurable
  have hphase : AEStronglyMeasurable (fun p : ES × ℝ =>
      Complex.I • complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)) μ :=
    hrawE.const_smul (Complex.I : ℂ)
  let w : ES × ℝ → ContinuousLeiLinSpace.ComplexE3 := fun p =>
    Complex.I • complexEuclideanPoint (rawNavierConvection (u p.2) (v p.2) p.1)
  have hq : Continuous (fun p : ES × ℝ => complexFrequency (spaceProj p.1)) :=
    continuous_complexFrequency.comp (spaceProj.continuous.comp continuous_fst)
  have hqM : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexFrequency (spaceProj p.1)) μ := hq.aestronglyMeasurable
  have hden : AEStronglyMeasurable (fun p : ES × ℝ =>
      ((‖complexFrequency (spaceProj p.1)‖ ^ 2 : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (hq.norm.pow 2)).aestronglyMeasurable
  have hformula : (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1)) =
      fun p => w p -
        (inner ℂ (complexFrequency (spaceProj p.1)) (w p) /
          ((‖complexFrequency (spaceProj p.1)‖ ^ 2 : ℝ) : ℂ)) •
          complexFrequency (spaceProj p.1) := by
    funext p
    change complexEuclideanPoint (ComplexLerayProjection.complexLeray (spaceProj p.1)
      (Complex.I • rawNavierConvection (u p.2) (v p.2) p.1)) = _
    rw [complexEuclideanPoint_complexLeray, complexEuclideanLeray_formula]
    simp [w, complexEuclideanPoint, WithLp.toLp_smul]
  rw [hformula]
  simp only [div_eq_mul_inv]
  exact hphase.sub ((hqM.inner hphase).mul hden.inv₀ |>.smul hqM)

/-- Aggregate degree-`k` Fourier moment in the same finite-coordinate shape as
the existing `coordinateX0Mass` and `coordinateX1Mass` function-space budgets. -/
def coordinateMomentMass (k : ℕ) (u : ES → ComplexSpace) : ℝ :=
  ∑ j : Fin 3, ∫ η : ES, ‖η‖ ^ k * ‖u η j‖

theorem coordinateMomentMass_nonneg (k : ℕ) (u : ES → ComplexSpace) :
    0 ≤ coordinateMomentMass k u := by
  unfold coordinateMomentMass
  exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ =>
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

@[simp] theorem coordinateMomentMass_zero (u : ES → ComplexSpace) :
    coordinateMomentMass 0 u = coordinateX0Mass u := by
  simp [coordinateMomentMass, coordinateX0Mass]

@[simp] theorem coordinateMomentMass_one (u : ES → ComplexSpace) :
    coordinateMomentMass 1 u = coordinateX1Mass u := by
  simp [coordinateMomentMass, coordinateX1Mass, normX1]

/-- The coordinatewise source majorant is exactly the product of aggregate
velocity moments, exposing the fixed-point function-space quantities. -/
theorem sourceMomentMajorant_eq_coordinateMomentMass
    (n : ℕ) (u v : ES → ComplexSpace) :
    sourceMomentMajorant n u v = (2 : ℝ) ^ n *
      (coordinateMomentMass (n + 1) u * coordinateMomentMass 0 v +
        coordinateMomentMass 0 u * coordinateMomentMass (n + 1) v) := by
  unfold sourceMomentMajorant coordinateMomentMass
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

/-- Joint continuity makes every time-indexed polynomial Fourier moment
measurable, by taking the frequency integral of a continuous product-space
integrand. -/
theorem coordinateMoment_aestronglyMeasurable_of_continuous
    (u : ℝ → ES → ComplexSpace) (j : Fin 3) (k : ℕ) (μ : Measure ℝ)
    (hu : Continuous (fun p : ES × ℝ => u p.2 p.1 j)) :
    AEStronglyMeasurable (fun s : ℝ =>
      ∫ η : ES, ‖η‖ ^ k * ‖u s η j‖) μ := by
  have hcont : Continuous (fun q : ℝ × ES =>
      ‖q.2‖ ^ k * ‖u q.1 q.2 j‖) := by
    exact (continuous_snd.norm.pow k).mul
      ((hu.comp (continuous_snd.prodMk continuous_fst)).norm)
  exact (hcont.aestronglyMeasurable : AEStronglyMeasurable
    (fun q : ℝ × ES => ‖q.2‖ ^ k * ‖u q.1 q.2 j‖) (μ.prod volume))
      |>.integral_prod_right'

/-- Joint continuity makes the aggregate finite-coordinate moment measurable
in time. -/
theorem coordinateMomentMass_aestronglyMeasurable_of_continuous
    (u : ℝ → ES → ComplexSpace) (k : ℕ) (μ : Measure ℝ)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j)) :
    AEStronglyMeasurable (fun s : ℝ => coordinateMomentMass k (u s)) μ := by
  unfold coordinateMomentMass
  exact Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
    coordinateMoment_aestronglyMeasurable_of_continuous u j k μ (hu j))

/-- Uniform coordinate mass and degree-`n+1` moment bounds on a finite recent
interval make the explicit source-moment majorant time integrable. -/
theorem integrable_sourceMomentMajorant_of_continuous_uniformMoments
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (τ t U0 V0 UN VN : ℝ)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i))
    (hU0 : 0 ≤ U0) (hUN : 0 ≤ UN)
    (hu0 : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (u s) ≤ U0)
    (hv0 : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (v s) ≤ V0)
    (huN : ∀ s ∈ Icc τ t, coordinateMomentMass (n + 1) (u s) ≤ UN)
    (hvN : ∀ s ∈ Icc τ t, coordinateMomentMass (n + 1) (v s) ≤ VN) :
    Integrable (fun s => sourceMomentMajorant n (u s) (v s))
      (volume.restrict (Icc τ t)) := by
  let μ : Measure ℝ := volume.restrict (Icc τ t)
  have hUm (j : Fin 3) (k : ℕ) : AEStronglyMeasurable (fun s : ℝ =>
      ∫ η : ES, ‖η‖ ^ k * ‖u s η j‖) μ :=
    coordinateMoment_aestronglyMeasurable_of_continuous u j k μ (hu j)
  have hVm (i : Fin 3) (k : ℕ) : AEStronglyMeasurable (fun s : ℝ =>
      ∫ η : ES, ‖η‖ ^ k * ‖v s η i‖) μ :=
    coordinateMoment_aestronglyMeasurable_of_continuous v i k μ (hv i)
  have hUzero (j : Fin 3) : AEStronglyMeasurable (fun s : ℝ =>
      ∫ η : ES, ‖u s η j‖) μ := by simpa using hUm j 0
  have hVzero (i : Fin 3) : AEStronglyMeasurable (fun s : ℝ =>
      ∫ η : ES, ‖v s η i‖) μ := by simpa using hVm i 0
  have hmajorMeas : AEStronglyMeasurable
      (fun s => sourceMomentMajorant n (u s) (v s)) μ := by
    unfold sourceMomentMajorant
    exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
      Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
        (continuous_const.aestronglyMeasurable.mul
          (((hUm j (n + 1)).mul (hVzero i)).add
            ((hUzero j).mul (hVm i (n + 1)))))))
  let C : ℝ := (2 : ℝ) ^ n * (UN * V0 + U0 * VN)
  have hCint : Integrable (fun _ : ℝ => C) μ := by
    dsimp [μ]
    exact integrableOn_const measure_Icc_lt_top.ne
  refine hCint.mono' hmajorMeas ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with s hs
  rw [sourceMomentMajorant_eq_coordinateMomentMass]
  have hleft : coordinateMomentMass (n + 1) (u s) * coordinateMomentMass 0 (v s) ≤
      UN * V0 := mul_le_mul (huN s hs) (hv0 s hs)
        (coordinateMomentMass_nonneg 0 (v s)) hUN
  have hright : coordinateMomentMass 0 (u s) * coordinateMomentMass (n + 1) (v s) ≤
      U0 * VN := mul_le_mul (hu0 s hs) (hvN s hs)
        (coordinateMomentMass_nonneg (n + 1) (v s)) hU0
  have hsourceNonneg : 0 ≤ (2 : ℝ) ^ n *
      (coordinateMomentMass (n + 1) (u s) * coordinateMomentMass 0 (v s) +
        coordinateMomentMass 0 (u s) * coordinateMomentMass (n + 1) (v s)) :=
    mul_nonneg (pow_nonneg (by norm_num) n) (add_nonneg
      (mul_nonneg (coordinateMomentMass_nonneg _ _) (coordinateMomentMass_nonneg _ _))
      (mul_nonneg (coordinateMomentMass_nonneg _ _) (coordinateMomentMass_nonneg _ _)))
  rw [Real.norm_eq_abs, abs_of_nonneg hsourceNonneg]
  exact mul_le_mul_of_nonneg_left (add_le_add hleft hright) (pow_nonneg (by norm_num) n)

/-- At degree zero, the actual admissible-space time budget is enough in the
`X¹` slot: only the `X⁰` masses need uniform control on the recent interval.
This replaces the preceding theorem's uniform degree-one bounds by the
time-integrated `coordinateX1Mass` bounds already used by the Lei--Lin
self-map and contraction estimates. -/
theorem integrable_sourceMomentMajorant_zero_of_continuous_uniformX0_integrableX1
    (u v : ℝ → ES → ComplexSpace) (τ t U0 V0 : ℝ)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i))
    (hu0 : ∀ s ∈ Icc τ t, coordinateX0Mass (u s) ≤ U0)
    (hv0 : ∀ s ∈ Icc τ t, coordinateX0Mass (v s) ≤ V0)
    (huX1 : Integrable (fun s => coordinateX1Mass (u s))
      (volume.restrict (Icc τ t)))
    (hvX1 : Integrable (fun s => coordinateX1Mass (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun s => sourceMomentMajorant 0 (u s) (v s))
      (volume.restrict (Icc τ t)) := by
  let μ : Measure ℝ := volume.restrict (Icc τ t)
  have hU0meas : AEStronglyMeasurable (fun s => coordinateX0Mass (u s)) μ := by
    simpa using coordinateMomentMass_aestronglyMeasurable_of_continuous u 0 μ hu
  have hV0meas : AEStronglyMeasurable (fun s => coordinateX0Mass (v s)) μ := by
    simpa using coordinateMomentMass_aestronglyMeasurable_of_continuous v 0 μ hv
  have hformula : (fun s => sourceMomentMajorant 0 (u s) (v s)) =
      fun s => coordinateX1Mass (u s) * coordinateX0Mass (v s) +
        coordinateX0Mass (u s) * coordinateX1Mass (v s) := by
    funext s
    rw [sourceMomentMajorant_eq_coordinateMomentMass]
    simp
  have hmajorMeas : AEStronglyMeasurable
      (fun s => sourceMomentMajorant 0 (u s) (v s)) μ := by
    rw [hformula]
    exact (huX1.aestronglyMeasurable.mul hV0meas).add
      (hU0meas.mul hvX1.aestronglyMeasurable)
  have hdom : Integrable (fun s =>
      coordinateX1Mass (u s) * V0 + U0 * coordinateX1Mass (v s)) μ :=
    (huX1.mul_const V0).add (hvX1.const_mul U0)
  refine hdom.mono' hmajorMeas ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with s hs
  rw [congrFun hformula s]
  have hu1nonneg : 0 ≤ coordinateX1Mass (u s) := by
    rw [← coordinateMomentMass_one]
    exact coordinateMomentMass_nonneg 1 (u s)
  have hv1nonneg : 0 ≤ coordinateX1Mass (v s) := by
    rw [← coordinateMomentMass_one]
    exact coordinateMomentMass_nonneg 1 (v s)
  have hu0nonneg : 0 ≤ coordinateX0Mass (u s) := by
    rw [← coordinateMomentMass_zero]
    exact coordinateMomentMass_nonneg 0 (u s)
  have hv0nonneg : 0 ≤ coordinateX0Mass (v s) := by
    rw [← coordinateMomentMass_zero]
    exact coordinateMomentMass_nonneg 0 (v s)
  have hleft : coordinateX1Mass (u s) * coordinateX0Mass (v s) ≤
      coordinateX1Mass (u s) * V0 :=
    mul_le_mul_of_nonneg_left (hv0 s hs) hu1nonneg
  have hright : coordinateX0Mass (u s) * coordinateX1Mass (v s) ≤
      U0 * coordinateX1Mass (v s) :=
    mul_le_mul_of_nonneg_right (hu0 s hs) hv1nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
    (mul_nonneg hu1nonneg hv0nonneg) (mul_nonneg hu0nonneg hv1nonneg))]
  exact add_le_add hleft hright

/-- Jointly continuous frequency trajectories with uniform recent mass and
moment bounds satisfy the literal recent-Duhamel moment consumer.  Joint source
measurability, slice measurability, and time integrability of the explicit
source majorant are derived rather than requested separately. -/
theorem integrable_pow_norm_continuousDuhamelRecent_of_continuous_uniformMoments
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (ν τ t U0 V0 UN VN : ℝ) (i : Fin 3)
    (hν : 0 ≤ ν)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (huN : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u s η j‖))
    (hvN : ∀ s i, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v s η i‖))
    (hU0 : 0 ≤ U0) (hUN : 0 ≤ UN)
    (hu0_bound : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (u s) ≤ U0)
    (hv0_bound : ∀ s ∈ Icc τ t, coordinateMomentMass 0 (v s) ≤ V0)
    (huN_bound : ∀ s ∈ Icc τ t, coordinateMomentMass (n + 1) (u s) ≤ UN)
    (hvN_bound : ∀ s ∈ Icc τ t, coordinateMomentMass (n + 1) (v s) ≤ VN) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n *
      ‖continuousDuhamelRecent ν τ u v t ξ i‖) := by
  have humeas (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => u s η j) volume :=
    ((hu j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hvmeas (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => v s η j) volume :=
    ((hv j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hjoint := continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    u v τ t hu hv
  have hmajor := integrable_sourceMomentMajorant_of_continuous_uniformMoments
    n u v τ t U0 V0 UN VN hu hv hU0 hUN
      hu0_bound hv0_bound huN_bound hvN_bound
  exact integrable_pow_norm_continuousDuhamelRecent_of_coordinateMoments
    n u v ν τ t i hν hjoint humeas hvmeas hu0 hv0 huN hvN hmajor

/-- Degree-zero recent-tail Fourier integrability from joint continuity,
uniform `X⁰`, and the time-integrated `X¹` admissible-space budget. -/
theorem integrable_norm_continuousDuhamelRecent_of_continuous_uniformX0_integrableX1
    (u v : ℝ → ES → ComplexSpace) (ν τ t U0 V0 : ℝ) (i : Fin 3)
    (hν : 0 ≤ ν)
    (hu : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => u p.2 p.1 j))
    (hv : ∀ i : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (hu1 : ∀ s j, Integrable (fun η : ES => ‖η‖ * ‖u s η j‖))
    (hv1 : ∀ s i, Integrable (fun η : ES => ‖η‖ * ‖v s η i‖))
    (hu0_bound : ∀ s ∈ Icc τ t, coordinateX0Mass (u s) ≤ U0)
    (hv0_bound : ∀ s ∈ Icc τ t, coordinateX0Mass (v s) ≤ V0)
    (huX1 : Integrable (fun s => coordinateX1Mass (u s))
      (volume.restrict (Icc τ t)))
    (hvX1 : Integrable (fun s => coordinateX1Mass (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun ξ : ES => ‖continuousDuhamelRecent ν τ u v t ξ i‖) := by
  have humeas (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => u s η j) volume :=
    ((hu j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hvmeas (s : ℝ) (j : Fin 3) :
      AEStronglyMeasurable (fun η : ES => v s η j) volume :=
    ((hv j).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hjoint := continuousNavierSource_joint_aestronglyMeasurable_of_continuous
    u v τ t hu hv
  have hmajor :=
    integrable_sourceMomentMajorant_zero_of_continuous_uniformX0_integrableX1
      u v τ t U0 V0 hu hv hu0_bound hv0_bound huX1 hvX1
  have h := integrable_pow_norm_continuousDuhamelRecent_of_coordinateMoments
    0 u v ν τ t i hν hjoint humeas hvmeas hu0 hv0
      (by simpa using hu1) (by simpa using hv1) hmajor
  simpa using h

end Navier.Analysis.ContinuousLeiLinRecentTailInputs

#check @Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_sourceMomentMajorant_zero_of_continuous_uniformX0_integrableX1
#check @Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_norm_continuousDuhamelRecent_of_continuous_uniformX0_integrableX1

#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.convolution_joint_aestronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.continuousNavierSource_joint_aestronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMomentMass
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMomentMass_nonneg
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMomentMass_zero
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMomentMass_one
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.sourceMomentMajorant_eq_coordinateMomentMass
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMoment_aestronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.coordinateMomentMass_aestronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_sourceMomentMajorant_of_continuous_uniformMoments
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_sourceMomentMajorant_zero_of_continuous_uniformX0_integrableX1
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_pow_norm_continuousDuhamelRecent_of_continuous_uniformMoments
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailInputs.integrable_norm_continuousDuhamelRecent_of_continuous_uniformX0_integrableX1
