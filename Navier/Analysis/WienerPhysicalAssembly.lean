import Navier.Analysis.WienerPhysicalPDE
import Navier.Analysis.ContinuousLeiLinReality
import Navier.Analysis.ContinuousLeiLinPhysicalVelocity
import Navier.Breakdown.MaximalNonextension

/-!
# Assembly of the official Navier–Stokes equation from the Wiener solution

For a fixed point `w` of the repository mild map with a transversal datum:

* `transverse_mild`: `∑ᵢ ξᵢ wᵢ(t,ξ) = 0` for almost every `ξ`;
* `div_physical_zero`: the complex physical field `U = 𝓕⁻ w` is divergence free;
* `hasDerivWithinAt_convective`: the complex identity in convective form
  `∂ₜUᵢ = (ν/4π²) ΔUᵢ + (1/2π) ∑ⱼ Uⱼ ∂ⱼUᵢ - (1/2π) ∂ᵢΠ`;
* `satisfiesNavierStokesBefore_physU`: at repository viscosity `ν = 4π²`, with
  real `U`, the rescaled pair `u = -(2π)⁻¹ Re U`, `p = -(4π²)⁻¹ Re Π` satisfies the
  official `SatisfiesNavierStokesBefore 1 zeroForce T`;
* `incompressibleBefore_physU`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution ComplexConjugate Topology

namespace Navier.Analysis.WienerPhysicalAssembly

open Navier
open Navier.Breakdown
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinReality
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPointwiseODE
open Navier.Analysis.WienerPhysicalPDE

/-! ## Transfer from the Euclidean carrier to `Navier.Space` -/

/-- `euclidPoint` as a continuous linear map. -/
def eCLM : Space →L[ℝ] ES := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap

theorem eCLM_apply (x : Space) : eCLM x = euclidPoint x := rfl

theorem euclidPoint_basisVector (l : Fin 3) :
    euclidPoint (basisVector l) = EuclideanSpace.single l 1 := rfl

theorem euclidPoint_eq_sum (v : Space) :
    euclidPoint v = ∑ j : Fin 3, v j • EuclideanSpace.single j (1 : ℝ) := by
  ext l
  simp [euclidPoint, Pi.single_apply]

theorem hasFDerivAt_reComp {F : ES → ℂ} {x : Space} (hF : DifferentiableAt ℝ F (euclidPoint x))
    (c : ℝ) :
    HasFDerivAt (fun x' : Space => c * (F (euclidPoint x')).re)
      (c • (Complex.reCLM.comp ((fderiv ℝ F (euclidPoint x)).comp eCLM))) x := by
  have h1 : HasFDerivAt (fun x' => F (eCLM x')) ((fderiv ℝ F (euclidPoint x)).comp eCLM) x :=
    hF.hasFDerivAt.comp x eCLM.hasFDerivAt
  exact (Complex.reCLM.hasFDerivAt.comp x h1).const_mul c

theorem fderiv_reComp_apply {F : ES → ℂ} (hF : ∀ y, DifferentiableAt ℝ F y) (c : ℝ)
    (x v : Space) :
    fderiv ℝ (fun x' : Space => c * (F (euclidPoint x')).re) x v =
      c * (fderiv ℝ F (euclidPoint x) (euclidPoint v)).re := by
  rw [(hasFDerivAt_reComp (hF _) c).fderiv]
  rfl

theorem fderiv_reCompVec_apply {F : Fin 3 → ES → ℂ} (hF : ∀ k y, DifferentiableAt ℝ (F k) y)
    (c : ℝ) (x v : Space) (k : Fin 3) :
    fderiv ℝ (fun x' : Space => fun k => c * (F k (euclidPoint x')).re) x v k =
      c * (fderiv ℝ (F k) (euclidPoint x) (euclidPoint v)).re := by
  rw [fderiv_pi (fun k => (hasFDerivAt_reComp (hF k _) c).differentiableAt)]
  exact fderiv_reComp_apply (hF k) c x v

/-! ## Differentiability of inverse transforms with all moments -/

theorem differentiable_fourierInv {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (y : ES) :
    DifferentiableAt ℝ (𝓕⁻ f) y :=
  (hasFDerivAt_fourierInv' (integrable_of_hmom hmom) (integrable_coord_mul hmom) y).differentiableAt

theorem differentiable_fderiv_fourierInv {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (l : Fin 3) (y : ES) :
    DifferentiableAt ℝ (fun z => fderiv ℝ (𝓕⁻ f) z (EuclideanSpace.single l 1)) y := by
  rw [fderiv_fourierInv_single_fun hmom l]
  exact (differentiable_fourierInv (moments_coord_mul hmom l) y).const_mul _

theorem fourierInv_zero_fun (y : ES) : 𝓕⁻ (fun _ : ES => (0 : ℂ)) y = 0 := by
  simp [Real.fourierInv_eq]

/-! ## The local solution -/

section Local

variable {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
  {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w)

include hfix hG in
/-- **Transversality of the mild solution**, for almost every frequency. -/
theorem transverse_mild (ha : ProfileDivergenceFree a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∀ᵐ ξ ∂(volume : Measure ES), ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * w t ξ i = 0 := by
  obtain ⟨-, -, -, -, -, hBc⟩ := good_bil hG hG
  filter_upwards [hBc] with ξ hc
  have hK : ∀ i : Fin 3, Integrable
      (fun s : ℝ => heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ)
      (volume.restrict (Icc (0 : ℝ) t)) := by
    intro i
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    unfold heatMode continuousNavierSource
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    exact (continuous_apply i).comp_continuousOn (hc.mono (Icc_subset_Icc_right ht.2))
  have hV := profileDivergenceFree_heatVec a ha ν t ξ
  have hleg (i : Fin 3) : (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
      (∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ)
      = ∫ s in Icc (0 : ℝ) t,
          (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
            heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ :=
    (ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.mul ℂ ℂ (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ))
      (hK i)).symm
  have hzero (s : ℝ) : ∑ i : Fin 3, (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
      heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ = 0 := by
    simp only [heatMode, continuousNavierSource, continuousNavierBilinear, continuousLeray]
    set c : ℂ := ((Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) : ℝ) : ℂ)
    set W := Complex.I • rawNavierConvection (w s) (w s) ξ
    have h1 : (∑ i : Fin 3, (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
        (c * Navier.Analysis.ComplexLerayProjection.complexLeray
          (Navier.Analysis.FourierMajorant.spaceProj ξ) W i))
        = ∑ i : Fin 3, c * ((Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
          Navier.Analysis.ComplexLerayProjection.complexLeray
            (Navier.Analysis.FourierMajorant.spaceProj ξ) W i) :=
      Finset.sum_congr rfl fun i _ => mul_left_comm _ c _
    rw [h1, ← Finset.mul_sum, Navier.Analysis.ComplexLerayProjection.complexLeray_transverse,
      mul_zero]
  have hD : ∑ i : Fin 3, (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
      continuousDuhamel ν w w t ξ i = 0 := by
    calc ∑ i : Fin 3, (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
          continuousDuhamel ν w w t ξ i
        = ∑ i : Fin 3, ∫ s in Icc (0 : ℝ) t,
            (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
              heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ :=
          Finset.sum_congr rfl fun i _ => hleg i
      _ = ∫ s in Icc (0 : ℝ) t, ∑ i : Fin 3,
            (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
              heatMode ν (t - s) (fun ζ => continuousNavierSource w w s ζ i) ξ :=
          (integral_finsetSum Finset.univ (fun i _ =>
            (hK i).const_mul (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ))).symm
      _ = ∫ s in Icc (0 : ℝ) t, (0 : ℂ) :=
          integral_congr_ae (ae_of_all _ fun s => hzero s)
      _ = 0 := integral_zero _ _
  rw [hfix t ht ξ]
  show ∑ i : Fin 3, (Navier.Analysis.FourierMajorant.spaceProj ξ i : ℂ) *
      (heatVec ν t a ξ i + continuousDuhamel ν w w t ξ i) = 0
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hV, hD, add_zero]

include hT hν hfix hG in
/-- **The complex physical field is divergence free.** -/
theorem div_physical_zero (ha : ProfileDivergenceFree a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (y : ES) :
    ∑ j : Fin 3, fderiv ℝ (𝓕⁻ (fun ξ => w t ξ j)) y (EuclideanSpace.single j 1) = 0 := by
  have hw : ∀ k, ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * w t ξ k) :=
    fun k α => hmom_w hT hν hG ht k α
  rw [Finset.sum_congr rfl fun j _ =>
    fderiv_fourierInv_single (integrable_of_hmom (hw j)) (integrable_coord_mul (hw j)) y j]
  rw [← Finset.mul_sum, ← fourierInv_sum _ (fun j _ => integrable_coord_mul (hw j) j),
    fourierInv_congr (transverse_mild hν a hfix hG ha ht) y, fourierInv_zero_fun, mul_zero]

include hT hν hfix hG in
/-- **The complex identity in convective form.** -/
theorem hasDerivWithinAt_convective (ha : ProfileDivergenceFree a) (i : Fin 3) (y : ES)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => 𝓕⁻ (fun ξ => w s ξ i) y)
      ((ν : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
          ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ (fun ξ => w t ξ i)) z
            (EuclideanSpace.single l 1)) y (EuclideanSpace.single l 1) +
        1 / (2 * (Real.pi : ℂ)) * ∑ j : Fin 3, 𝓕⁻ (fun ξ => w t ξ j) y *
          fderiv ℝ (𝓕⁻ (fun ξ => w t ξ i)) y (EuclideanSpace.single j 1) -
        1 / (2 * (Real.pi : ℂ)) * fderiv ℝ (𝓕⁻ (Qhat w t)) y (EuclideanSpace.single i 1))
      (Ico (0 : ℝ) T) t := by
  refine (hasDerivWithinAt_physical_identity hT hν a hfix hG i y ht).congr_deriv ?_
  have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
  have hw : ∀ k, ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * w t ξ k) :=
    fun k α => hmom_w hT hν hG htI k α
  have hprod : ∀ j : Fin 3,
      fderiv ℝ (fun z => 𝓕⁻ (fun ξ => w t ξ j) z * 𝓕⁻ (fun ξ => w t ξ i) z) y
          (EuclideanSpace.single j 1) =
        𝓕⁻ (fun ξ => w t ξ j) y *
            fderiv ℝ (𝓕⁻ (fun ξ => w t ξ i)) y (EuclideanSpace.single j 1) +
          𝓕⁻ (fun ξ => w t ξ i) y *
            fderiv ℝ (𝓕⁻ (fun ξ => w t ξ j)) y (EuclideanSpace.single j 1) := by
    intro j
    rw [fderiv_fun_mul (differentiable_fourierInv (hw j) y) (differentiable_fourierInv (hw i) y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => hprod j, Finset.sum_add_distrib, ← Finset.mul_sum,
    div_physical_zero hT hν a hfix hG ha htI y]
  ring

/-! ## The official equation at repository viscosity `4π²` -/

/-- The rescaled real physical velocity `u = -(2π)⁻¹ Re 𝓕⁻ w`. -/
def physU (w : ℝ → ES → ComplexSpace) : VelocityEvolution :=
  fun t x k => -(1 / (2 * Real.pi)) * (𝓕⁻ (fun ξ => w t ξ k) (euclidPoint x)).re

/-- The rescaled real pressure `p = -(4π²)⁻¹ Re 𝓕⁻ Q̂`. -/
def physP (w : ℝ → ES → ComplexSpace) : PressureEvolution :=
  fun t x => -(1 / (4 * Real.pi ^ 2)) * (𝓕⁻ (Qhat w t) (euclidPoint x)).re

include hT hν hG in
theorem fderiv_physU_apply {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x v : Space) (k : Fin 3) :
    fderiv ℝ (physU w t) x v k =
      -(1 / (2 * Real.pi)) *
        (fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) (euclidPoint x) (euclidPoint v)).re :=
  fderiv_reCompVec_apply (F := fun k => 𝓕⁻ (fun ξ => w t ξ k))
    (fun k y => differentiable_fourierInv (hmom_w hT hν hG ht k) y) _ x v k

include hT hν hG in
theorem fderiv_physU_fun {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (l : Fin 3) :
    (fun x => fderiv ℝ (physU w t) x (basisVector l)) = fun x k =>
      -(1 / (2 * Real.pi)) *
        ((fun z => fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) z (EuclideanSpace.single l 1))
          (euclidPoint x)).re := by
  funext x k
  rw [fderiv_physU_apply hT hν hG ht, euclidPoint_basisVector]

include hT hν hG in
theorem laplacian_physU {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Space) (k : Fin 3) :
    laplacian (physU w) t x k =
      -(1 / (2 * Real.pi)) * (∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ
        (𝓕⁻ (fun ξ => w t ξ k)) z (EuclideanSpace.single l 1)) (euclidPoint x)
          (EuclideanSpace.single l 1)).re := by
  unfold laplacian
  rw [Finset.sum_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_physU_fun hT hν hG ht l]
  rw [fderiv_reCompVec_apply (F := fun k z =>
      fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) z (EuclideanSpace.single l 1))
    (fun k y => differentiable_fderiv_fourierInv (hmom_w hT hν hG ht k) l y), euclidPoint_basisVector]

include hT hν hG in
theorem pressureGradient_physP {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Space) (k : Fin 3) :
    pressureGradient (physP w) t x k =
      -(1 / (4 * Real.pi ^ 2)) *
        (fderiv ℝ (𝓕⁻ (Qhat w t)) (euclidPoint x) (EuclideanSpace.single k 1)).re := by
  unfold pressureGradient
  rw [show physP w t = fun x' : Space =>
      -(1 / (4 * Real.pi ^ 2)) * (𝓕⁻ (Qhat w t) (euclidPoint x')).re from rfl,
    fderiv_reComp_apply (fun y => differentiable_fourierInv (hmom_Qhat hG ht) y),
    euclidPoint_basisVector]

include hT hν hG in
theorem convection_physU {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Space) (k : Fin 3) :
    convection (physU w) t x k =
      -(1 / (2 * Real.pi)) * ∑ j : Fin 3, physU w t x j *
        (fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) (euclidPoint x) (EuclideanSpace.single j 1)).re := by
  unfold convection spatialDerivative
  rw [fderiv_physU_apply hT hν hG ht, euclidPoint_eq_sum (physU w t x), map_sum, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.real_smul, Complex.re_ofReal_mul]

include hT hν hfix hG in
/-- **The time derivative of the rescaled velocity.** -/
theorem timeDerivative_physU (ha : ProfileDivergenceFree a) {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    (x : Space) (k : Fin 3) :
    timeDerivative (physU w) t x k = -(1 / (2 * Real.pi)) *
      ((ν : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
          ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) z
            (EuclideanSpace.single l 1)) (euclidPoint x) (EuclideanSpace.single l 1) +
        1 / (2 * (Real.pi : ℂ)) * ∑ j : Fin 3, 𝓕⁻ (fun ξ => w t ξ j) (euclidPoint x) *
          fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) (euclidPoint x) (EuclideanSpace.single j 1) -
        1 / (2 * (Real.pi : ℂ)) *
          fderiv ℝ (𝓕⁻ (Qhat w t)) (euclidPoint x) (EuclideanSpace.single k 1)).re := by
  have hnhds : Ico (0 : ℝ) T ∈ 𝓝[Ici (0 : ℝ)] t := by
    rw [← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds htT)
  have hk : ∀ k' : Fin 3, HasDerivWithinAt (fun s => physU w s x k')
      (-(1 / (2 * Real.pi)) *
        ((ν : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
          ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k')) z
            (EuclideanSpace.single l 1)) (euclidPoint x) (EuclideanSpace.single l 1) +
        1 / (2 * (Real.pi : ℂ)) * ∑ j : Fin 3, 𝓕⁻ (fun ξ => w t ξ j) (euclidPoint x) *
          fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k')) (euclidPoint x) (EuclideanSpace.single j 1) -
        1 / (2 * (Real.pi : ℂ)) *
          fderiv ℝ (𝓕⁻ (Qhat w t)) (euclidPoint x) (EuclideanSpace.single k' 1)).re)
      (Ici (0 : ℝ)) t := by
    intro k'
    have h := hasDerivWithinAt_convective hT hν a hfix hG ha k' (euclidPoint x) ⟨ht0, htT⟩
    have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t h).const_mul
      (-(1 / (2 * Real.pi)))
    exact h2.mono_of_mem_nhdsWithin hnhds
  have hvec := hasDerivWithinAt_pi.2 hk
  have hd := hvec.derivWithin (uniqueDiffOn_Ici 0 t ht0)
  exact congrFun hd k

include hT hν hfix hG in
/-- **Incompressibility of the rescaled velocity.** -/
theorem incompressibleBefore_physU (ha : ProfileDivergenceFree a) :
    IncompressibleBefore T (physU w) := by
  intro t ht0 htT x
  have htI : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
  unfold divergence spatialDerivative
  rw [Finset.sum_congr rfl fun i _ => fderiv_physU_apply hT hν hG htI x (basisVector i) i]
  simp_rw [euclidPoint_basisVector]
  rw [← Finset.mul_sum, ← Complex.re_sum, div_physical_zero hT hν a hfix hG ha htI,
    Complex.zero_re, mul_zero]

include hT hν hfix hG in
/-- **The official Navier–Stokes equation on `[0,T)`** for the rescaled pair, at
repository viscosity `ν = 4π²` (physical viscosity `1`), given reality of the
physical field. -/
theorem satisfiesNavierStokesBefore_physU (hν4 : ν = 4 * Real.pi ^ 2)
    (ha : ProfileDivergenceFree a)
    (hreal : ∀ t ∈ Icc (0 : ℝ) T, ∀ (k : Fin 3) (y : ES),
      conj (𝓕⁻ (fun ξ => w t ξ k) y) = 𝓕⁻ (fun ξ => w t ξ k) y) :
    SatisfiesNavierStokesBefore 1 zeroForce T (physU w) (physP w) := by
  intro t ht0 htT x
  have htI : t ∈ Icc (0 : ℝ) T := ⟨ht0, htT.le⟩
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul, zeroForce,
    Pi.zero_apply, add_zero]
  rw [timeDerivative_physU hT hν a hfix hG ha ht0 htT x k, convection_physU hT hν hG htI x k,
    laplacian_physU hT hν hG htI x k, pressureGradient_physP hT hν hG htI x k]
  have him : ∀ j : Fin 3, (𝓕⁻ (fun ξ => w t ξ j) (euclidPoint x)).im = 0 := fun j =>
    Complex.conj_eq_iff_im.mp (hreal t htI j (euclidPoint x))
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : ((ν : ℝ) : ℂ) / (4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [hν4]; push_cast; field_simp
  have h2 : (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, one_mul, h2, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  simp only [Complex.re_sum, Complex.mul_re, him, zero_mul, sub_zero]
  have h3 : ∑ j : Fin 3, physU w t x j *
      (fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) (euclidPoint x) (EuclideanSpace.single j 1)).re =
      -(1 / (2 * Real.pi)) * ∑ j : Fin 3, (𝓕⁻ (fun ξ => w t ξ j) (euclidPoint x)).re *
        (fderiv ℝ (𝓕⁻ (fun ξ => w t ξ k)) (euclidPoint x) (EuclideanSpace.single j 1)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold physU; ring
  rw [h3]
  field_simp
  ring

/-- **Joint smoothness of the rescaled velocity** from joint smoothness of the
complex physical coordinates. -/
theorem smoothVelocityBefore_physU
    (hsm : ∀ i : Fin 3, ContDiffOn ℝ ∞
      (fun z : ℝ × ES => Navier.Analysis.ContinuousLeiLinPhysicalCarrier.physicalCoord
        (w z.1) i z.2) (Ico (0 : ℝ) T ×ˢ (univ : Set ES))) :
    SmoothVelocityBefore T (physU w) := by
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1, euclidPoint z.2)) :=
    contDiff_fst.prodMk (eCLM.contDiff.comp contDiff_snd)
  have hms : MapsTo (fun z : ℝ × Space => (z.1, euclidPoint z.2)) (spacetimeBefore T)
      (Ico (0 : ℝ) T ×ˢ (univ : Set ES)) := fun z hz => ⟨hz.1, mem_univ _⟩
  refine contDiffOn_pi.2 fun k => ?_
  have h := (hsm k).comp hmap.contDiffOn hms
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn h)

end Local

end Navier.Analysis.WienerPhysicalAssembly

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalAssembly.satisfiesNavierStokesBefore_physU
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalAssembly.incompressibleBefore_physU
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalAssembly.smoothVelocityBefore_physU
