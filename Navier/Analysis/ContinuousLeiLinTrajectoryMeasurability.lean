import Navier.Analysis.ContinuousLeiLinTrajectoryLift
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.CompactOpen

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter Topology
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open scoped ENNReal NNReal

namespace Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutSection (μ : Measure (Navier.Analysis.ContinuousLeiLinSpace.ES))
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfI : ∀ t, Integrable (f t) μ) (n : ℕ) (t : ℝ) : Lp E 1 μ :=
  ((hfI t).indicator measurableSet_closedBall).toL1
    ((Metric.closedBall 0 (n : ℝ)).indicator (f t))

private theorem cutSection_sub (μ : Measure Navier.Analysis.ContinuousLeiLinSpace.ES)
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfI : ∀ t, Integrable (f t) μ) (n : ℕ) (s t : ℝ) :
    cutSection μ f hfI n s - cutSection μ f hfI n t =
      (((hfI s).sub (hfI t)).indicator measurableSet_closedBall).toL1
        ((Metric.closedBall 0 (n : ℝ)).indicator (fun x => f s x - f t x)) := by
  let K := Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ)
  let fs : Navier.Analysis.ContinuousLeiLinSpace.ES → E := K.indicator (f s)
  let ft : Navier.Analysis.ContinuousLeiLinSpace.ES → E := K.indicator (f t)
  have hfs : Integrable fs μ := (hfI s).indicator measurableSet_closedBall
  have hft : Integrable ft μ := (hfI t).indicator measurableSet_closedBall
  calc
    cutSection μ f hfI n s - cutSection μ f hfI n t =
        hfs.toL1 fs - hft.toL1 ft := by rfl
    _ = (hfs.sub hft).toL1 (fs - ft) :=
      (Integrable.toL1_sub fs ft hfs hft).symm
    _ = (((hfI s).sub (hfI t)).indicator measurableSet_closedBall).toL1
        (K.indicator (fun x => f s x - f t x)) := by
      congr 1
      funext x
      exact congrFun (Set.indicator_sub K (f s) (f t)).symm x

private theorem dist_cutSection_eq_subtype
    (μ : Measure Navier.Analysis.ContinuousLeiLinSpace.ES)
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfI : ∀ t, Integrable (f t) μ) (n : ℕ) (s t : ℝ)
    (hsubI : ∀ r, Integrable (fun x : Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ) =>
      f r x) (Measure.comap Subtype.val μ)) :
    dist (cutSection μ f hfI n s) (cutSection μ f hfI n t) =
      dist ((hsubI s).toL1 (fun x : Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ) => f s x))
        ((hsubI t).toL1 (fun x : Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ) => f t x)) := by
  let K := Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ)
  let cutDiff : Lp E 1 μ :=
    (((hfI s).sub (hfI t)).indicator measurableSet_closedBall).toL1
      (K.indicator (fun x => f s x - f t x))
  let subDiff : Lp E 1 (Measure.comap Subtype.val μ) :=
    (hsubI s).toL1 (fun x : K => f s x) -
      (hsubI t).toL1 (fun x : K => f t x)
  rw [dist_eq_norm, dist_eq_norm, cutSection_sub]
  change ‖cutDiff‖ = ‖subDiff‖
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖cutDiff x‖ ∂μ) =
        ∫ x, ‖K.indicator (fun x => f s x - f t x) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [Integrable.coeFn_toL1
        (((hfI s).sub (hfI t)).indicator measurableSet_closedBall)] with x hx
      rw [show cutDiff x = K.indicator (fun x => f s x - f t x) x from hx]
    _ = ∫ x in K, ‖f s x - f t x‖ ∂μ := by
      have hnorm : (fun x => ‖K.indicator (fun x => f s x - f t x) x‖) =
          K.indicator (fun x => ‖f s x - f t x‖) := by
        funext x
        exact norm_indicator_eq_indicator_norm (fun x => f s x - f t x) x
      rw [hnorm, integral_indicator measurableSet_closedBall]
    _ = ∫ x : K, ‖f s x - f t x‖ ∂Measure.comap Subtype.val μ := by
      exact (integral_subtype_comap measurableSet_closedBall _).symm
    _ = ∫ x : K, ‖subDiff x‖ ∂Measure.comap Subtype.val μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hsubI s).toL1 (fun x : K => f s x))
          ((hsubI t).toL1 (fun x : K => f t x)),
        Integrable.coeFn_toL1 (hsubI s), Integrable.coeFn_toL1 (hsubI t)] with x hsub hs ht
      rw [show subDiff x =
        ((hsubI s).toL1 (fun x : K => f s x) x) -
          ((hsubI t).toL1 (fun x : K => f t x) x) from hsub]
      rw [hs, ht]

private theorem continuous_cutSection
    (μ : Measure (Navier.Analysis.ContinuousLeiLinSpace.ES))
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfC : Continuous (Function.uncurry f))
    (hfI : ∀ t, Integrable (f t) μ)
    (hball : ∀ n : ℕ, μ (Metric.closedBall 0 (n : ℝ)) < ∞)
    (n : ℕ) : Continuous (cutSection μ f hfI n) := by
  let K := Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ)
  let μK : Measure K := Measure.comap Subtype.val μ
  letI : IsFiniteMeasure μK :=
    ⟨by
      change Measure.comap Subtype.val μ Set.univ < ∞
      rw [comap_subtype_coe_apply measurableSet_closedBall]
      have himage : Subtype.val '' (Set.univ : Set K) = K := by
        ext x
        simp
      rw [himage]
      exact hball n⟩
  let cfun : ℝ → C(K, E) := fun t =>
    ContinuousMap.mkD (K.domRestrict (f t)) 0
  have hcfun : Continuous cfun := by
    apply ContinuousMap.continuous_mkD_restrict_of_uncurry
    intro p hp
    exact hfC.continuousAt.continuousWithinAt
  let subLp : ℝ → Lp E 1 μK := fun t =>
    ContinuousMap.toLp 1 μK ℝ (cfun t)
  have hsubLp : Continuous subLp := (ContinuousMap.toLp 1 μK ℝ).continuous.comp hcfun
  have hsubI (r : ℝ) : Integrable (fun x : K => f r x) μK := by
    exact (measurePreserving_subtype_coe measurableSet_closedBall).integrable_comp
      ((hfI r).restrict).aestronglyMeasurable |>.2 ((hfI r).restrict)
  have hsubLp_eq (r : ℝ) : subLp r = (hsubI r).toL1 (fun x : K => f r x) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (μ := μK) (p := 1) (𝕜 := ℝ) (cfun r),
      Integrable.coeFn_toL1 (hsubI r)] with x hx hy
    rw [hx, hy]
    have hsection : Continuous (f r) :=
      hfC.comp (continuous_const.prodMk continuous_id)
    simp [cfun, ContinuousMap.mkD_of_continuousOn hsection.continuousOn]
  apply continuous_iff_continuousAt.2
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hsubLp.continuousAt) ε hε
  exact ⟨δ, hδ, fun s hs => by
    rw [dist_cutSection_eq_subtype μ f hfI n s t hsubI]
    rw [← hsubLp_eq s, ← hsubLp_eq t]
    exact hclose hs⟩


def fullSection (μ : Measure Navier.Analysis.ContinuousLeiLinSpace.ES)
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfI : ∀ t, Integrable (f t) μ) (t : ℝ) : Lp E 1 μ :=
  (hfI t).toL1 (f t)

private theorem dist_cutSection_full_eq_compl
    (μ : Measure Navier.Analysis.ContinuousLeiLinSpace.ES)
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfI : ∀ t, Integrable (f t) μ) (n : ℕ) (t : ℝ) :
    dist (cutSection μ f hfI n t) (fullSection μ f hfI t) =
      ∫ x in (Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ))ᶜ,
        ‖f t x‖ ∂μ := by
  let K := Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ)
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖(cutSection μ f hfI n t - fullSection μ f hfI t) x‖ ∂μ) =
        ∫ x, ‖K.indicator (f t) x - f t x‖ ∂μ := by
      apply integral_congr_ae
      have hcutRep : (cutSection μ f hfI n t :
          Navier.Analysis.ContinuousLeiLinSpace.ES → E) =ᵐ[μ] K.indicator (f t) := by
        simpa [cutSection, K] using
          (Integrable.coeFn_toL1 ((hfI t).indicator
            (measurableSet_closedBall : MeasurableSet K)))
      have hfullRep : (fullSection μ f hfI t :
          Navier.Analysis.ContinuousLeiLinSpace.ES → E) =ᵐ[μ] f t := by
        simpa [fullSection] using Integrable.coeFn_toL1 (hfI t)
      filter_upwards [Lp.coeFn_sub (cutSection μ f hfI n t) (fullSection μ f hfI t),
        hcutRep, hfullRep] with x hsub hcut hfull
      rw [hsub]
      change ‖cutSection μ f hfI n t x - fullSection μ f hfI t x‖ = _
      rw [hcut, hfull]
    _ = ∫ x, Kᶜ.indicator (fun x => ‖f t x‖) x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ K <;> simp [Set.indicator, hx]
    _ = ∫ x in Kᶜ, ‖f t x‖ ∂μ := integral_indicator measurableSet_closedBall.compl

/-- A jointly continuous Fourier field with integrable spatial sections gives a
strongly measurable trajectory in the spatial `L¹` quotient, provided compact
frequency balls have finite measure. -/
theorem stronglyMeasurable_fullSection_of_continuous
    (μ : Measure Navier.Analysis.ContinuousLeiLinSpace.ES)
    (f : ℝ → Navier.Analysis.ContinuousLeiLinSpace.ES → E)
    (hfC : Continuous (Function.uncurry f))
    (hfI : ∀ t, Integrable (f t) μ)
    (hball : ∀ n : ℕ, μ (Metric.closedBall 0 (n : ℝ)) < ∞) :
    StronglyMeasurable (fullSection μ f hfI) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n => (continuous_cutSection μ f hfC hfI hball n).stronglyMeasurable)
  rw [tendsto_pi_nhds]
  intro t
  rw [tendsto_iff_dist_tendsto_zero]
  rw [show (fun n => dist (cutSection μ f hfI n t) (fullSection μ f hfI t)) =
      fun n : ℕ => ∫ x in (Metric.closedBall
        (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ))ᶜ, ‖f t x‖ ∂μ by
    funext n
    exact dist_cutSection_full_eq_compl μ f hfI n t]
  have hanti : Antitone (fun n : ℕ =>
      (Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ))ᶜ) := by
    intro m n hmn
    exact compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn))
  have htail := tendsto_setIntegral_of_antitone
    (fun n : ℕ => measurableSet_closedBall.compl) hanti
    ⟨0, (hfI t).norm.restrict⟩
  have hinter : (⋂ n : ℕ,
      (Metric.closedBall (0 : Navier.Analysis.ContinuousLeiLinSpace.ES) (n : ℝ))ᶜ) = ∅ := by
    rw [← compl_iUnion, Metric.iUnion_closedBall_nat, compl_univ]
  simpa [hinter] using htail


 theorem xm1FrequencyMeasure_closedBall_lt_top (n : ℕ) :
    xm1FrequencyMeasure (Metric.closedBall (0 : ES) (n : ℝ)) < ∞ := by
  have hlocal : LocallyIntegrable (fun ξ : ES => ‖ξ‖⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (μ := volume) (E := ES)
      (F := ℝ) (by norm_num) (C := 1) (α := (1 : ℝ)) (by norm_num) ?_ ?_
    · filter_upwards with ξ
      simp [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)),
        Real.rpow_neg_one]
    · exact continuous_norm.aestronglyMeasurable.inv₀
  have hI : Integrable (fun ξ : ES => ‖ξ‖⁻¹)
      (volume.restrict (Metric.closedBall 0 (n : ℝ))) :=
    hlocal.integrableOn_isCompact (isCompact_closedBall _ _)
  rw [xm1FrequencyMeasure, withDensity_apply _ measurableSet_closedBall]
  have heq : (fun ξ : ES => xm1Density ξ) =
      fun ξ => ‖(‖ξ‖⁻¹ : ℝ)‖ₑ := by
    funext ξ
    rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (norm_nonneg ξ))]
    rfl
  rw [heq]
  exact hI.hasFiniteIntegral

 theorem viscousX1FrequencyMeasure_closedBall_lt_top (ν : ℝ≥0) (n : ℕ) :
    viscousX1FrequencyMeasure ν (Metric.closedBall (0 : ES) (n : ℝ)) < ∞ := by
  have hI : Integrable (fun ξ : ES => (ν : ℝ) * ‖ξ‖)
      (volume.restrict (Metric.closedBall 0 (n : ℝ))) :=
    (continuous_const.mul continuous_norm).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  rw [viscousX1FrequencyMeasure, withDensity_apply _ measurableSet_closedBall]
  have heq : (fun ξ : ES => (ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖) =
      fun ξ => ‖((ν : ℝ) * ‖ξ‖ : ℝ)‖ₑ := by
    funext ξ
    rw [Real.enorm_eq_ofReal (mul_nonneg (NNReal.zero_le_coe) (norm_nonneg ξ)),
      ENNReal.ofReal_mul (NNReal.zero_le_coe)]
    simp
  change (∫⁻ ξ : ES in Metric.closedBall 0 (n : ℝ),
    (ν : ℝ≥0∞) * ENNReal.ofReal ‖ξ‖ ∂volume) < ∞
  rw [heq]
  exact hI.hasFiniteIntegral



/-- Joint coordinate continuity gives strong measurability of the actual
`X⁻¹`-valued trajectory.  The proof uses compact frequency truncations and
then lets their radii tend to infinity in `L¹`. -/
theorem xm1Section_stronglyMeasurable_of_continuous
    (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (huC : ∀ i : Fin 3, Continuous (fun p : ℝ × ES => u p.1 p.2 i)) :
    StronglyMeasurable
      (ContinuousLeiLinTrajectoryLift.xm1Section u huM huXm1) := by
  have hcoordC : Continuous (fun p : ℝ × ES =>
      ContinuousLeiLinTrajectoryLift.coordinateL1 (u p.1) p.2) := by
    apply (PiLp.continuous_toLp 1 (fun _ : Fin 3 => ℂ)).comp
    apply continuous_pi
    intro i
    exact huC i
  have hcoordI (t : ℝ) : Integrable
      (ContinuousLeiLinTrajectoryLift.coordinateL1 (u t)) xm1FrequencyMeasure :=
    ContinuousLeiLinTrajectoryLift.coordinateL1_xm1_integrable
      (u t) (huM t) (huXm1 t)
  have hsm := stronglyMeasurable_fullSection_of_continuous xm1FrequencyMeasure
    (fun t => ContinuousLeiLinTrajectoryLift.coordinateL1 (u t))
    hcoordC hcoordI xm1FrequencyMeasure_closedBall_lt_top
  have heq : fullSection xm1FrequencyMeasure
      (fun t => ContinuousLeiLinTrajectoryLift.coordinateL1 (u t)) hcoordI =
      ContinuousLeiLinTrajectoryLift.xm1Section u huM huXm1 := by
    funext t
    apply Lp.ext
    filter_upwards [Integrable.coeFn_toL1 (hcoordI t),
      ContinuousLeiLinTrajectoryLift.coeFn_toXm1Spatial
        (u t) (huM t) (huXm1 t)] with ξ hleft hright
    simpa [fullSection, ContinuousLeiLinTrajectoryLift.xm1Section] using
      hleft.trans hright.symm
  rw [← heq]
  exact hsm

/-- The same joint coordinate continuity gives strong measurability of the
actual viscosity-weighted `X¹`-valued trajectory. -/
theorem viscousX1Section_stronglyMeasurable_of_continuous
    (ν : ℝ≥0) (u : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))
    (huC : ∀ i : Fin 3, Continuous (fun p : ℝ × ES => u p.1 p.2 i)) :
    StronglyMeasurable
      (ContinuousLeiLinTrajectoryLift.viscousX1Section u huM huX1 ν) := by
  have hcoordC : Continuous (fun p : ℝ × ES =>
      ContinuousLeiLinTrajectoryLift.coordinateL1 (u p.1) p.2) := by
    apply (PiLp.continuous_toLp 1 (fun _ : Fin 3 => ℂ)).comp
    apply continuous_pi
    intro i
    exact huC i
  have hcoordI (t : ℝ) : Integrable
      (ContinuousLeiLinTrajectoryLift.coordinateL1 (u t))
      (viscousX1FrequencyMeasure ν) :=
    ContinuousLeiLinTrajectoryLift.coordinateL1_viscousX1_integrable
      ν (u t) (huM t) (huX1 t)
  have hsm := stronglyMeasurable_fullSection_of_continuous
    (viscousX1FrequencyMeasure ν)
    (fun t => ContinuousLeiLinTrajectoryLift.coordinateL1 (u t))
    hcoordC hcoordI (viscousX1FrequencyMeasure_closedBall_lt_top ν)
  have heq : fullSection (viscousX1FrequencyMeasure ν)
      (fun t => ContinuousLeiLinTrajectoryLift.coordinateL1 (u t)) hcoordI =
      ContinuousLeiLinTrajectoryLift.viscousX1Section u huM huX1 ν := by
    funext t
    apply Lp.ext
    filter_upwards [Integrable.coeFn_toL1 (hcoordI t),
      ContinuousLeiLinTrajectoryLift.coeFn_toViscousX1Spatial
        ν (u t) (huM t) (huX1 t)] with ξ hleft hright
    simpa [fullSection, ContinuousLeiLinTrajectoryLift.viscousX1Section] using
      hleft.trans hright.symm
  rw [← heq]
  exact hsm

/-- The concrete continuous mild image enters the linked complete carrier
without separately assuming measurability of either weighted `L¹` section.
Both section facts follow from one faithful joint continuity hypothesis on its
three Fourier coordinates. -/
def actualLinkedContinuousMildImage_of_continuous
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (hM : ∀ t i, AEStronglyMeasurable (fun ξ =>
      ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i) volume)
    (hXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i‖))
    (hX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ *
      ‖ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t ξ i‖))
    (hC : ∀ i : Fin 3, Continuous (fun p : ℝ × ES =>
      ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v p.1 p.2 i))
    (hXm1Bound : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass
        (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
          a v t) ≤ R)
    (hX1Int : Integrable (fun t => coordinateX1Mass
      (ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν)
        a v t)) (leiLinTimeMeasure T)) :
    ActualLinkedCarrier ν T := by
  let w := ContinuousLeiLinSelfMap.continuousMildImage
    (ν : ℝ) (by exact_mod_cast hν) a v
  have hXm1Time : AEStronglyMeasurable
      (ContinuousLeiLinTrajectoryLift.xm1Section w hM hXm1)
      (leiLinTimeMeasure T) :=
    (xm1Section_stronglyMeasurable_of_continuous w hM hXm1 hC).aestronglyMeasurable
  have hX1Time : AEStronglyMeasurable
      (ContinuousLeiLinTrajectoryLift.viscousX1Section w hM hX1 ν)
      (leiLinTimeMeasure T) :=
    (viscousX1Section_stronglyMeasurable_of_continuous ν w hM hX1 hC).aestronglyMeasurable
  exact ContinuousLeiLinTrajectoryLift.actualLinkedContinuousMildImage
    ν hν T R a v hM hXm1 hX1 hXm1Time hX1Time hXm1Bound hX1Int

end Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability

#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.stronglyMeasurable_fullSection_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.xm1FrequencyMeasure_closedBall_lt_top
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.viscousX1FrequencyMeasure_closedBall_lt_top
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.xm1Section_stronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.viscousX1Section_stronglyMeasurable_of_continuous
#print axioms Navier.Analysis.ContinuousLeiLinTrajectoryMeasurability.actualLinkedContinuousMildImage_of_continuous
