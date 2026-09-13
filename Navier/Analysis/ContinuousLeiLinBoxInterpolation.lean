import Navier.Analysis.ContinuousLeiLinBoxProduct
import Navier.Analysis.ContinuousLeiLinPhysicalIntegrability

/-!
# Unweighted interpolation inputs for the actual Lei--Lin box

The existing nonlinear continuous mild-map estimates require genuine spatial
`L¹` integrability of each Fourier coordinate.  An element of the completed
actual box supplies only the two homogeneous endpoint slots.  Their common
everywhere representative nevertheless has the required unweighted
integrability at every time by the already proved square-root Hölder
interpolation theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap

namespace Navier.Analysis.ContinuousLeiLinBoxInterpolation

/-- Expanding bounded-frequency sets used to read an unweighted `L¹` norm
continuously from the `X⁻¹` quotient. -/
def x0TruncationSet (n : ℕ) : Set ES :=
  Metric.closedBall 0 (n + 1 : ℝ)

/-- On a ball of radius `n+1`, Lebesgue measure is dominated by `n+1`
times the homogeneous `X⁻¹` measure.  The exceptional zero frequency has
Lebesgue measure zero. -/
theorem x0TruncationMeasure_le (n : ℕ) :
    volume.restrict (x0TruncationSet n) ≤
      (n + 1 : ℝ≥0∞) • xm1FrequencyMeasure := by
  unfold x0TruncationSet
  rw [← withDensity_indicator_one Metric.isClosed_closedBall.measurableSet,
    xm1FrequencyMeasure, ← withDensity_smul]
  apply withDensity_mono
  have hz : ∀ᵐ ξ : ES ∂volume, ξ ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hz] with ξ hξ
  by_cases hmem : ξ ∈ Metric.closedBall (0 : ES) (n + 1 : ℝ)
  · rw [Set.indicator_of_mem hmem]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hle : ‖ξ‖ ≤ (n + 1 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    have hreal : (1 : ℝ) ≤ (n + 1 : ℝ) * ‖ξ‖⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]
      simpa using hle
    simpa [xm1Density, ENNReal.ofReal_add (Nat.cast_nonneg n),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (n + 1 : ℝ))] using
        ENNReal.ofReal_le_ofReal hreal
  · simp [hmem]
  · exact ENNReal.measurable_ofReal.comp measurable_norm.inv

/-- Continuous restriction of the `X⁻¹` spatial quotient to unweighted `L¹`
on a bounded frequency ball. -/
def xm1ToTruncatedX0 (n : ℕ) :
    Xm1Spatial →L[ℝ]
      Lp FourierCoordinateL1 1 (volume.restrict (x0TruncationSet n)) :=
  Lp.LpToLpOfMeasureLeSMul
    (c := (n + 1 : ℝ≥0∞)) (by simp) (x0TruncationMeasure_le n)

/-- The norm of each bounded-frequency restriction is measurable in time,
because it is the norm of a continuous linear image of the actual `X⁻¹`
Bochner representative. -/
theorem truncatedX0Norm_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) (n : ℕ) :
    AEStronglyMeasurable (fun t =>
      ‖xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t)‖)
      (leiLinTimeMeasure T) := by
  exact ((xm1ToTruncatedX0 n).continuous.comp_aestronglyMeasurable
    (everywhereXm1Section_aestronglyMeasurable ν hν T x)).norm

/-- The preceding quotient norm is the literal coordinate `X⁰` mass on the
bounded frequency ball. -/
theorem norm_xm1ToTruncatedX0_everywhere_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T)
    (n : ℕ) (t : ℝ) :
    ‖xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t)‖ =
      ∑ i : Fin 3, ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i‖ := by
  rw [L1.norm_eq_integral_norm]
  have hout : xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t)
      =ᵐ[volume.restrict (x0TruncationSet n)]
        everywhereXm1Section ν hν T x t := by
    exact Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (n + 1 : ℝ≥0∞)) (by simp)
      (x0TruncationMeasure_le n) _
  have hac : volume.restrict (x0TruncationSet n) ≪ xm1FrequencyMeasure :=
    Measure.absolutelyContinuous_of_le_smul (x0TruncationMeasure_le n)
  have hin : everywhereXm1Section ν hν T x t
      =ᵐ[volume.restrict (x0TruncationSet n)]
        coordinateL1 (everywhereRawRepresentative ν T x t) := by
    apply hac.ae_eq
    exact coeFn_toXm1Spatial
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_xm1_integrable ν T x t)
  calc
    (∫ ξ, ‖xm1ToTruncatedX0 n
        (everywhereXm1Section ν hν T x t) ξ‖
        ∂volume.restrict (x0TruncationSet n)) =
        ∫ ξ, ‖coordinateL1 (everywhereRawRepresentative ν T x t) ξ‖
          ∂volume.restrict (x0TruncationSet n) := by
      apply integral_congr_ae
      filter_upwards [hout, hin] with ξ houtξ hinξ
      rw [houtξ, hinξ]
    _ = ∫ ξ in x0TruncationSet n,
        ∑ i : Fin 3, ‖everywhereRawRepresentative ν T x t ξ i‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [norm_coordinateL1]
    _ = ∑ i : Fin 3, ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i‖ := by
      exact integral_finsetSum Finset.univ fun i _ =>
        (integrable_norm_of_integrable_Xm1_X1
          (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i)
          (everywhereRawRepresentative_xm1_integrable ν T x t i)
          (everywhereRawRepresentative_x1_integrable ν T x t i)).integrableOn

theorem x0TruncationSet_monotone : Monotone x0TruncationSet := by
  intro m n hmn ξ hξ
  have hr : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hmn
  exact Metric.closedBall_subset_closedBall hr hξ

theorem iUnion_x0TruncationSet : (⋃ n : ℕ, x0TruncationSet n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ξ
  obtain ⟨n, hn⟩ := exists_nat_ge ‖ξ‖
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  simp only [x0TruncationSet, Metric.mem_closedBall, dist_zero_right]
  exact hn.trans (by exact_mod_cast Nat.le_succ n)

/-- The measurable bounded-frequency norms converge pointwise to the full
coordinate `X⁰` mass. -/
theorem tendsto_truncatedX0Norm_everywhere
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) :
    Tendsto (fun n =>
      ‖xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t)‖)
      atTop (𝓝 (coordinateX0Mass (everywhereRawRepresentative ν T x t))) := by
  have hi (i : Fin 3) :
      Tendsto (fun n => ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i‖) atTop
        (𝓝 (∫ ξ : ES, ‖everywhereRawRepresentative ν T x t ξ i‖)) := by
    have hInt : IntegrableOn
        (fun ξ : ES => ‖everywhereRawRepresentative ν T x t ξ i‖)
        (⋃ n : ℕ, x0TruncationSet n) := by
      rw [iUnion_x0TruncationSet]
      simpa using integrable_norm_of_integrable_Xm1_X1
        (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i)
        (everywhereRawRepresentative_xm1_integrable ν T x t i)
        (everywhereRawRepresentative_x1_integrable ν T x t i)
    have h := tendsto_setIntegral_of_monotone
      (f := fun ξ : ES => ‖everywhereRawRepresentative ν T x t ξ i‖)
      (fun n => Metric.isClosed_closedBall.measurableSet)
      x0TruncationSet_monotone hInt
    have hu : (⋃ n : ℕ, Metric.closedBall (0 : ES) (n + 1 : ℝ)) = Set.univ := by
      simpa [x0TruncationSet] using iUnion_x0TruncationSet
    rw [hu] at h
    simpa [x0TruncationSet] using h
  have hsum := tendsto_finsetSum Finset.univ fun i _ => hi i
  apply hsum.congr'
  filter_upwards with n
  rw [norm_xm1ToTruncatedX0_everywhere_eq]

/-- The full coordinate `X⁰` mass is measurable in time as the pointwise
limit of continuous bounded-frequency restriction norms. -/
theorem coordinateX0Mass_everywhere_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (fun t =>
      coordinateX0Mass (everywhereRawRepresentative ν T x t))
      (leiLinTimeMeasure T) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => truncatedX0Norm_aestronglyMeasurable ν hν T x n)
  exact Eventually.of_forall fun t =>
    tendsto_truncatedX0Norm_everywhere ν hν T x t

/-- Interpolation plus the actual box budgets makes the squared `X⁰` mass
integrable over the whole finite horizon. -/
theorem integrable_coordinateX0Mass_sq_everywhere_of_mem_box
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    Integrable (fun t =>
      coordinateX0Mass (everywhereRawRepresentative ν T x.1 t) ^ 2)
      (leiLinTimeMeasure T) := by
  have hprod := integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
    ν hν T xm1Radius x1WeightedRadius x
  apply hprod.mono'
    ((coordinateX0Mass_everywhere_aestronglyMeasurable ν hν T x.1).pow 2)
  filter_upwards with t
  change ‖coordinateX0Mass (everywhereRawRepresentative ν T x.1 t) ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass
    (everywhereRawRepresentative ν T x.1 t)
    (everywhereRawRepresentative_xm1_integrable ν T x.1 t)
    (everywhereRawRepresentative_x1_integrable ν T x.1 t)

/-- The squared `X⁰` input requested by the existing Duhamel estimates is
therefore integrable on every causal subinterval. -/
theorem integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    IntegrableOn (fun s =>
      coordinateX0Mass (everywhereRawRepresentative ν T x.1 s) ^ 2)
      (Icc (0 : ℝ) t) volume := by
  have hfull := integrable_coordinateX0Mass_sq_everywhere_of_mem_box
    ν hν T xm1Radius x1WeightedRadius x
  change Integrable _ (volume.restrict (Icc (0 : ℝ) T)) at hfull
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  exact hfull.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- At every time, the actual representative generates an integrable weighted
Euclidean Navier source and every weighted source coordinate.  These are the
fixed-time source hypotheses used by both nonlinear output estimates. -/
theorem continuousNavierSource_fixedTime_inputs_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    (∀ s : ℝ, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ))) ∧
    (∀ s : ℝ, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ i‖)) := by
  have humeas := everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1
  have hu0 (s : ℝ) (i : Fin 3) := integrable_norm_of_integrable_Xm1_X1
    (fun ξ : ES => everywhereRawRepresentative ν T x.1 s ξ i)
    (everywhereRawRepresentative_xm1_integrable ν T x.1 s i)
    (everywhereRawRepresentative_x1_integrable ν T x.1 s i)
  have hs1 (s : ℝ) : Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ)) := by
    exact integrable_normXm1_continuousNavierBilinear
      (everywhereRawRepresentative ν T x.1 s)
      (everywhereRawRepresentative ν T x.1 s)
      (humeas s) (humeas s) (hu0 s) (hu0 s)
  refine ⟨hs1, ?_⟩
  intro s i
  have hvec := continuousNavierBilinear_aestronglyMeasurable
    (everywhereRawRepresentative ν T x.1 s)
    (everywhereRawRepresentative ν T x.1 s)
    (humeas s) (humeas s) (hu0 s) (hu0 s)
  have hcoord : AEStronglyMeasurable (fun ξ : ES =>
      continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ i) volume := by
    have h := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).aestronglyMeasurable
      |>.comp_aemeasurable hvec.aemeasurable
    exact h.congr (Eventually.of_forall fun ξ =>
      complexEuclideanPoint_apply (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ) i)
  apply (hs1 s).mono'
    (continuous_norm.aestronglyMeasurable.inv₀.mul hcoord.norm)
  filter_upwards with ξ
  change ‖‖ξ‖⁻¹ * ‖continuousNavierSource
    (everywhereRawRepresentative ν T x.1)
    (everywhereRawRepresentative ν T x.1) s ξ i‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ))
    (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (show ‖continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ i‖ ≤
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ) by
      calc
        _ = ‖complexEuclideanPoint (continuousNavierSource
              (everywhereRawRepresentative ν T x.1)
              (everywhereRawRepresentative ν T x.1) s ξ) i‖ := by
            rw [complexEuclideanPoint_apply]
        _ ≤ ‖complexEuclideanPoint (continuousNavierSource
              (everywhereRawRepresentative ν T x.1)
              (everywhereRawRepresentative ν T x.1) s ξ)‖ :=
            PiLp.norm_apply_le _ i)
    (inv_nonneg.mpr (norm_nonneg ξ))

/-- The diagonal source estimate on an actual box now needs only the source
integral itself to be known integrable; all six velocity-side spatial and
time hypotheses of the original consumer are discharged by the quotient
carrier. -/
theorem integral_normXm1_continuousNavierSource_self_le_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hsource : IntegrableOn (fun s => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ)) (Icc (0 : ℝ) t)) :
    (∫ s in Icc (0 : ℝ) t, ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ)) ≤
      ∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
          coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
  have hmeas := everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1
  have h0 (s : ℝ) (i : Fin 3) := integrable_norm_of_integrable_Xm1_X1
    (fun ξ : ES => everywhereRawRepresentative ν T x.1 s ξ i)
    (everywhereRawRepresentative_xm1_integrable ν T x.1 s i)
    (everywhereRawRepresentative_x1_integrable ν T x.1 s i)
  have h0sq := integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
    ν hν T xm1Radius x1WeightedRadius x t ht
  have hmixed := (integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
    ν hν T xm1Radius x1WeightedRadius x).mono_measure
      (Measure.restrict_mono
        (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T from
          fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩) le_rfl)
  exact integral_normXm1_continuousNavierSource_self_le_coordinateXm1X1
    (everywhereRawRepresentative ν T x.1) (Icc (0 : ℝ) t)
    hmeas h0
    (everywhereRawRepresentative_xm1_integrable ν T x.1)
    (everywhereRawRepresentative_x1_integrable ν T x.1)
    isClosed_Icc.measurableSet hsource h0sq hmixed

/-- Exact `B₁` producer for the existing mild self-map theorem on the actual
box.  Compared with `continuousMildImage_coordinateXm1Mass_le`, every
velocity-side measurability, `X⁰`, endpoint, square, and mixed-product premise
has been eliminated; only the datum and output/source kernel integrability
obligations remain. -/
theorem continuousMildImage_coordinateXm1Mass_le_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hd : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i‖))
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
      (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => continuousNavierSource
          (everywhereRawRepresentative ν T x.1)
          (everywhereRawRepresentative ν T x.1) p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ => normXm1
      (heatMode (ν : ℝ) (t - s) (fun ζ : ES => continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ζ i)))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ => normXm1
      (fun ζ : ES => continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ζ i))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) s ξ))
      (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
      (everywhereRawRepresentative ν T x.1) t) ≤
      coordinateXm1Mass a + 3 * ∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
          coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
  have hmeas := everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1
  have h0 (s : ℝ) (i : Fin 3) := integrable_norm_of_integrable_Xm1_X1
    (fun ξ : ES => everywhereRawRepresentative ν T x.1 s ξ i)
    (everywhereRawRepresentative_xm1_integrable ν T x.1 s i)
    (everywhereRawRepresentative_x1_integrable ν T x.1 s i)
  obtain ⟨hs1, hb0⟩ := continuousNavierSource_fixedTime_inputs_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x
  exact continuousMildImage_coordinateXm1Mass_le
    (ν : ℝ) (by exact_mod_cast hν) a ha
    (everywhereRawRepresentative ν T x.1) t ht.1 hd hb hf hg
    (fun s _ i => hb0 s i) (fun s _ => hs1 s) hi
    hmeas h0
    (everywhereRawRepresentative_xm1_integrable ν T x.1)
    (everywhereRawRepresentative_x1_integrable ν T x.1)
    (integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
      ν hν T xm1Radius x1WeightedRadius x t ht)
    ((integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
      ν hν T xm1Radius x1WeightedRadius x).mono_measure
        (Measure.restrict_mono
          (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T from
            fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩) le_rfl))

/-- Every coordinate of the canonical everywhere representative is genuinely
integrable with respect to unweighted Lebesgue frequency measure. -/
theorem everywhereRawRepresentative_coordinate_integrable
    (ν : ℝ≥0) (T : ℝ) (x : ActualLinkedCarrier ν T) (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖everywhereRawRepresentative ν T x t ξ i‖) := by
  exact integrable_norm_of_integrable_Xm1_X1
    (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i)
    (everywhereRawRepresentative_xm1_integrable ν T x t i)
    (everywhereRawRepresentative_x1_integrable ν T x t i)

/-- The actual box therefore supplies the spatial measurability and
unweighted-integrability hypotheses used by each fixed-time nonlinear source
estimate, without a continuity assumption on quotient representatives. -/
theorem everywhereRawRepresentative_fixedTime_inputs
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    (∀ t i, AEStronglyMeasurable
      (fun ξ : ES => everywhereRawRepresentative ν T x.1 t ξ i) volume) ∧
    (∀ t i, Integrable
      (fun ξ : ES => ‖everywhereRawRepresentative ν T x.1 t ξ i‖)) := by
  exact ⟨everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1,
    everywhereRawRepresentative_coordinate_integrable ν T x.1⟩

/-- Original fixed-time nonlinear source consumer with both raw spatial input
families discharged by the actual quotient-box representative. -/
theorem normXm1_continuousNavierSource_self_le_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) (t : ℝ) :
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
      (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ)) ≤
      coordinateX0Mass (everywhereRawRepresentative ν T x.1 t) ^ 2 := by
  obtain ⟨hmeas, hint⟩ :=
    everywhereRawRepresentative_fixedTime_inputs
      ν hν T xm1Radius x1WeightedRadius x
  simpa [pow_two] using
    normXm1_continuousNavierSource_le_coordinateX0Mass
      (everywhereRawRepresentative ν T x.1)
      (everywhereRawRepresentative ν T x.1) t hmeas hmeas hint hint

end Navier.Analysis.ContinuousLeiLinBoxInterpolation

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.everywhereRawRepresentative_coordinate_integrable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.everywhereRawRepresentative_fixedTime_inputs
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.normXm1_continuousNavierSource_self_le_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.x0TruncationMeasure_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.norm_xm1ToTruncatedX0_everywhere_eq
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.tendsto_truncatedX0Norm_everywhere
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.coordinateX0Mass_everywhere_aestronglyMeasurable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.integrable_coordinateX0Mass_sq_everywhere_of_mem_box
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.continuousNavierSource_fixedTime_inputs_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.integral_normXm1_continuousNavierSource_self_le_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxInterpolation.continuousMildImage_coordinateXm1Mass_le_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinTimeDuhamel.integral_normXm1_continuousNavierSource_self_le_coordinateXm1X1
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinSelfMap.continuousMildImage_coordinateXm1Mass_le
