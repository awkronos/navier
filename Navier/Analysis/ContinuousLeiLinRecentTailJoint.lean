import Navier.Analysis.ContinuousLeiLinRecentTailMoment

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Navier.Analysis.ContinuousLeiLinRecentTailJoint

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinRecentTailMoment

/-- The exact finite-coordinate majorant for the degree-`n` moment of the
Navier source.  Each input carries degree `n+1`, accounting for the output
derivative in the symbol. -/
def sourceMomentMajorant (n : ℕ) (u v : ES → ComplexSpace) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (2 : ℝ) ^ n *
    ((∫ η : ES, ‖η‖ ^ (n + 1) * ‖u η j‖) * (∫ η : ES, ‖v η i‖) +
      (∫ η : ES, ‖u η j‖) * (∫ η : ES, ‖η‖ ^ (n + 1) * ‖v η i‖))

/-- Quantitative fixed-time moment propagation through the genuine
Leray-projected continuous Navier symbol. -/
theorem integral_pow_norm_continuousNavierSource_le
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (t : ℝ)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u t η j))
    (hv : ∀ i : Fin 3, AEStronglyMeasurable (fun η : ES => v t η i))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u t η j‖))
    (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v t η i‖))
    (huN : ∀ j : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u t η j‖))
    (hvN : ∀ i : Fin 3, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v t η i‖)) :
    (∫ ξ : ES, ‖ξ‖ ^ n *
      complexEuclideanNorm (continuousNavierSource u v t ξ)) ≤
      sourceMomentMajorant n (u t) (v t) := by
  have hlhs := integrable_pow_norm_continuousNavierSource n u v t hu hv hu0 hv0 huN hvN
  have hconv (i j : Fin 3) : Integrable (fun ξ : ES => ‖ξ‖ ^ (n + 1) *
      convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ) :=
    integrable_polynomial_weighted_convolution (n + 1)
      (fun η => ‖u t η j‖) (fun η => ‖v t η i‖)
      (hu0 j) (hv0 i) (huN j) (hvN i) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      ‖ξ‖ ^ (n + 1) *
        convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ) := by
    exact integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hconv i j
  have hpoint (ξ : ES) : ‖ξ‖ ^ n *
      complexEuclideanNorm (continuousNavierSource u v t ξ) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ (n + 1) *
        convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ := by
    calc
      _ ≤ ‖ξ‖ ^ n * (∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ *
          convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ) :=
        mul_le_mul_of_nonneg_left (continuousNavierBilinear_majorant (u t) (v t) ξ)
          (pow_nonneg (norm_nonneg ξ) n)
      _ = _ := by simp only [Finset.mul_sum, pow_succ, mul_assoc]
  calc
    (∫ ξ : ES, ‖ξ‖ ^ n *
        complexEuclideanNorm (continuousNavierSource u v t ξ)) ≤
        ∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ ^ (n + 1) *
          convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ :=
      integral_mono hlhs hsum hpoint
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ (n + 1) *
          convolution (fun η => ‖u t η j‖) (fun η => ‖v t η i‖) ξ := by
      rw [integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ => hconv i j]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ fun j _ => hconv i j
    _ ≤ sourceMomentMajorant n (u t) (v t) := by
      unfold sourceMomentMajorant
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa using polynomial_weighted_convolution_mass_le (n + 1)
        (fun η => ‖u t η j‖) (fun η => ‖v t η i‖)
        (hu0 j) (hv0 i) (huN j) (hvN i)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- Tonelli/Fubini bridge from fixed-time source estimates to a joint
frequency-time moment.  Joint measurability and integrability of the explicit
coordinate majorant are separate hypotheses. -/
theorem integrable_joint_pow_norm_continuousNavierSource
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (τ t : ℝ)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t))))
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hv : ∀ s i, AEStronglyMeasurable (fun η : ES => v s η i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (huN : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u s η j‖))
    (hvN : ∀ s i, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v s η i‖))
    (hmajor : Integrable (fun s => sourceMomentMajorant n (u s) (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun p : ES × ℝ => ‖p.1‖ ^ n *
      complexEuclideanNorm (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t))) := by
  let μ := volume.restrict (Icc τ t)
  let F : ES × ℝ → ℝ := fun p => ‖p.1‖ ^ n *
    complexEuclideanNorm (continuousNavierSource u v p.2 p.1)
  have hFmeas : AEStronglyMeasurable F (volume.prod μ) := by
    have hw : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖ ^ n : ES × ℝ → ℝ)
        (volume.prod μ) := by fun_prop
    have hn : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanNorm (continuousNavierSource u v p.2 p.1))
        (volume.prod μ) := by
      simpa [complexEuclideanNorm] using hjoint.norm
    exact hw.mul hn
  apply (integrable_prod_iff' hFmeas).2
  constructor
  · exact Filter.Eventually.of_forall fun s =>
      integrable_pow_norm_continuousNavierSource n u v s
        (hu s) (hv s) (hu0 s) (hv0 s) (huN s) (hvN s)
  · have hsecmeas : AEStronglyMeasurable (fun s => ∫ ξ : ES, ‖F (ξ, s)‖)
        μ := hFmeas.norm.prod_swap.integral_prod_right'
    refine hmajor.mono' hsecmeas ?_
    filter_upwards with s
    have hFnonneg (ξ : ES) : 0 ≤ F (ξ, s) := by
      exact mul_nonneg (pow_nonneg (norm_nonneg ξ) n) (by
        unfold complexEuclideanNorm
        exact norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ => norm_nonneg (F (ξ, s)))]
    have heq : (∫ ξ : ES, ‖F (ξ, s)‖) = ∫ ξ : ES, F (ξ, s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact Real.norm_of_nonneg (hFnonneg ξ)
    rw [heq]
    exact integral_pow_norm_continuousNavierSource_le n u v s
      (hu s) (hv s) (hu0 s) (hv0 s) (huN s) (hvN s)

/-- Every Fourier coordinate is controlled by the Euclidean vector norm. -/
theorem norm_coord_le_complexEuclideanNorm (z : ComplexSpace) (i : Fin 3) :
    ‖z i‖ ≤ complexEuclideanNorm z := by
  calc
    ‖z i‖ = ‖complexEuclideanPoint z i‖ :=
      congrArg (fun w : ℂ => ‖w‖) (complexEuclideanPoint_apply z i).symm
    _ ≤ ‖complexEuclideanPoint z‖ := PiLp.norm_apply_le (complexEuclideanPoint z) i

/-- Joint measurability of the Euclidean realization supplies every source
coordinate, so coordinate moment propagation needs no duplicate measurability
premise. -/
theorem continuousNavierSource_coord_aestronglyMeasurable
    (u v : ℝ → ES → ComplexSpace) (τ t : ℝ)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t)))) (i : Fin 3) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc τ t))) := by
  have h := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).aestronglyMeasurable
    |>.comp_aemeasurable hjoint.aemeasurable
  exact h.congr (Filter.Eventually.of_forall fun p =>
    complexEuclideanPoint_apply (continuousNavierSource u v p.2 p.1) i)

/-- Coordinate projection preserves the joint source moment supplied by the
Euclidean source bound. -/
theorem integrable_joint_pow_norm_continuousNavierSource_coord
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (τ t : ℝ) (i : Fin 3)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t))))
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hv : ∀ s i, AEStronglyMeasurable (fun η : ES => v s η i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (huN : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u s η j‖))
    (hvN : ∀ s i, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v s η i‖))
    (hmajor : Integrable (fun s => sourceMomentMajorant n (u s) (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun p : ES × ℝ => ‖p.1‖ ^ n *
      ‖continuousNavierSource u v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc τ t))) := by
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable u v τ t hjoint i
  have hvec := integrable_joint_pow_norm_continuousNavierSource n u v τ t
    hjoint hu hv hu0 hv0 huN hvN hmajor
  refine hvec.mono' ?_ ?_
  · have hw : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖ ^ n : ES × ℝ → ℝ)
        (volume.prod (volume.restrict (Icc τ t))) := by fun_prop
    exact hw.mul hcoord.norm
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (norm_nonneg p.1) n) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (norm_coord_le_complexEuclideanNorm (continuousNavierSource u v p.2 p.1) i)
      (pow_nonneg (norm_nonneg p.1) n)

/-- The joint coordinate-moment bridge feeds the literal recent Duhamel
consumer.  This is the feasible `[τ,t]` conclusion, with no global-in-time
regularity claim. -/
theorem integrable_pow_norm_continuousDuhamelRecent_of_coordinateMoments
    (n : ℕ) (u v : ℝ → ES → ComplexSpace) (ν τ t : ℝ) (i : Fin 3)
    (hν : 0 ≤ ν)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u v p.2 p.1))
      (volume.prod (volume.restrict (Icc τ t))))
    (hu : ∀ s j, AEStronglyMeasurable (fun η : ES => u s η j))
    (hv : ∀ s i, AEStronglyMeasurable (fun η : ES => v s η i))
    (hu0 : ∀ s j, Integrable (fun η : ES => ‖u s η j‖))
    (hv0 : ∀ s i, Integrable (fun η : ES => ‖v s η i‖))
    (huN : ∀ s j, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖u s η j‖))
    (hvN : ∀ s i, Integrable (fun η : ES => ‖η‖ ^ (n + 1) * ‖v s η i‖))
    (hmajor : Integrable (fun s => sourceMomentMajorant n (u s) (v s))
      (volume.restrict (Icc τ t))) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n *
      ‖continuousDuhamelRecent ν τ u v t ξ i‖) := by
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable u v τ t hjoint i
  apply integrable_pow_norm_continuousDuhamelRecent_of_source u v ν τ t i n hν hcoord
  exact integrable_joint_pow_norm_continuousNavierSource_coord n u v τ t i
    hjoint hu hv hu0 hv0 huN hvN hmajor

end Navier.Analysis.ContinuousLeiLinRecentTailJoint

#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.sourceMomentMajorant
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.integral_pow_norm_continuousNavierSource_le
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.norm_coord_le_complexEuclideanNorm
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.continuousNavierSource_coord_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.integrable_joint_pow_norm_continuousNavierSource_coord
#print axioms Navier.Analysis.ContinuousLeiLinRecentTailJoint.integrable_pow_norm_continuousDuhamelRecent_of_coordinateMoments
